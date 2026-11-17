import * as setContent from "./setContent.mjs";

const SPOTLIGHT_FEED_URL = "https://fd.api.iris.microsoft.com/v4/api/selection";
const SPOTLIGHT_PLACEMENT = "88000820";
const SPOTLIGHT_CACHE_PREFIX = "windows_spotlight_feed_v6";
// v4 intentionally invalidates entries from older builds that could contain
// empty/invisible "successful" translations.
const SPOTLIGHT_TRANSLATION_CACHE_KEY = "windows_spotlight_translation_cache_v5";
const PEAPIX_SPOTLIGHT_FEED_URL = "https://peapix.com/spotlight/feed";
const PEAPIX_SPOTLIGHT_FEED_CACHE_KEY = "windows_spotlight_peapix_feed_v2";
const PEAPIX_SPOTLIGHT_FEED_CACHE_TTL = 6 * 60 * 60 * 1000;
const SPOTLIGHT_TRANSLATION_URL = "https://api.mymemory.translated.net/get";
const STARTUP_IMAGE_CHANGE_GUARD_MS = 7000;

let activeBgIndex = 0;
let backgroundLayerA;
let backgroundLayerB;
let spotlightItems = [];
let spotlightItemIndex = 0;
let spotlightFetchPromise = null;
let peapixSpotlightFeedPromise = null;
let imageChangeInProgress = false;
let reloadSpotlightAfterCurrentImage = false;
let startupSpotlightCacheChecked = false;
let hasDisplayedSpotlightImage = false;
let hasReceivedOnlineSpotlightImage = false;
let ignoreInitialVerseImageChange = true;
let startupImageChangeGuardUntil = 0;
let spotlightImageRequestId = 0;
const spotlightTranslationBackoff = new Map();

function getUILocalizedText(value) {
  return setContent.translateUIString(value);
}

function getSpotlightRequestLocale() {
  return setContent.getSpotlightLocale();
}

function getSpotlightCountry(locale) {
  const regionMatch = locale.match(/-([a-z]{2})(?:-|$)/i);
  return regionMatch ? regionMatch[1].toUpperCase() : "US";
}

function getSpotlightCacheKey(locale, country) {
  return `${SPOTLIGHT_CACHE_PREFIX}_${country}_${locale}`;
}

function readCachedSpotlightItems(locale, country) {
  try {
    const stored = localStorage.getItem(getSpotlightCacheKey(locale, country));
    if (!stored) return [];
    const parsed = JSON.parse(stored);
    return Array.isArray(parsed)
      ? parsed.filter((item) => item && typeof item.imageUrl === "string")
      : [];
  } catch (error) {
    return [];
  }
}

function writeCachedSpotlightItems(locale, country, items) {
  try {
    localStorage.setItem(getSpotlightCacheKey(locale, country), JSON.stringify(items));
  } catch {
    // Cache persistence is optional; keep the current session working.
  }
}

function normalizeHttpsUrl(value) {
  if (typeof value !== "string" || !value.trim()) return "";
  const normalized = value.trim().replace(/^microsoft-edge:/i, "");
  try {
    const url = new URL(normalized);
    return url.protocol === "https:" ? url.href : "";
  } catch {
    return "";
  }
}

function getSpotlightAssetMatchKeys(value) {
  try {
    const url = new URL(value);
    const pathname = decodeURIComponent(url.pathname).toLocaleLowerCase();
    const normalizedPath = pathname.replace(/[_-]\d{3,5}x\d{3,5}(?=\.[^.]+$)/i, "");
    const filename = normalizedPath.split("/").pop() || "";
    const uuidPattern = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}[_-]?/i;
    const creativeId = filename.match(/^([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})/i);
    // Locale/crop variants can carry different CDN GUIDs while retaining the
    // same descriptive asset filename. Keep both strict and GUID-free keys.
    const descriptor = filename.replace(uuidPattern, "");
    const keys = [`asset-path:${normalizedPath}`, `asset-file:${filename}`];
    if (descriptor && descriptor !== filename) keys.push(`asset-descriptor:${descriptor}`);
    if (creativeId) keys.unshift(`creative:${creativeId[1].toLocaleLowerCase()}`);
    return [...new Set(keys)];
  } catch {
    const text = toDisplayText(value).toLocaleLowerCase();
    return text ? [`asset-raw:${text}`] : [];
  }
}

function getSpotlightLocaleLanguage(locale) {
  return String(locale || "en-US").split("-")[0].toLocaleLowerCase();
}

function getSpotlightTranslationLanguage(locale) {
  const normalized = String(locale || "en-US");
  const language = getSpotlightLocaleLanguage(normalized);
  if (language === "zh") {
    return /(?:^|[-_])(?:TW|HK|MO|Hant)(?:$|[-_])/i.test(normalized) ? "zh-TW" : "zh-CN";
  }
  return language;
}

function getSpotlightMetadataFallbackLocales(locale, country) {
  const language = getSpotlightLocaleLanguage(locale);
  if (language !== "en") return [`en-${country}`];
  return [];
}

function needsSpotlightMetadataFallback(items) {
  return items.some((item) =>
    isGenericSpotlightMetadata(item.title) || isGenericSpotlightMetadata(item.description),
  );
}

function isLikelyEnglishSpotlightText(value, locale) {
  const text = toDisplayText(value);
  const language = getSpotlightLocaleLanguage(locale);
  if (!text || language === "en") return false;

  const latinCount = [...text.matchAll(/\p{Script=Latin}/gu)].length;
  if (!latinCount) return false;

  if (language === "ko") {
    const hangulCount = [...text.matchAll(/\p{Script=Hangul}/gu)].length;
    return latinCount >= 5 && latinCount > hangulCount * 1.25;
  }
  if (language === "zh") {
    const hanCount = [...text.matchAll(/\p{Script=Han}/gu)].length;
    return latinCount >= 5 && latinCount > hanCount * 1.25;
  }
  if (language === "ja") {
    const japaneseCount = [...text.matchAll(/[\p{Script=Han}\p{Script=Hiragana}\p{Script=Katakana}]/gu)].length;
    return latinCount >= 5 && latinCount > japaneseCount * 1.25;
  }
  return false;
}

function isLikelyEnglishSpotlightTitle(value, locale) {
  const language = getSpotlightLocaleLanguage(locale);
  if (language !== "ko") return isLikelyEnglishSpotlightText(value, locale);
  const text = toDisplayText(value);
  if (!text) return false;
  const latinCount = [...text.matchAll(/\p{Script=Latin}/gu)].length;
  const hangulCount = [...text.matchAll(/\p{Script=Hangul}/gu)].length;
  // Titles and place names are often shorter than full descriptions (e.g. "Maui").
  return latinCount >= 3 && latinCount > hangulCount * 1.2;
}

function normalizeSpotlightSearchText(value) {
  return toDisplayText(value)
    .normalize("NFD")
    .replace(/\p{M}/gu, "")
    .normalize("NFC")
    .toLocaleLowerCase()
    .replace(/[^\p{L}\p{N}]+/gu, " ")
    .trim();
}

function getSpotlightSourceMatchKey(value) {
  const normalized = normalizeHttpsUrl(value);
  if (!normalized) return "";
  try {
    const url = new URL(normalized);
    url.hash = "";
    for (const key of [...url.searchParams.keys()]) {
      if (/^(?:utm_|ocid$|cvid$|form$|from$|source$|tracking|cid$|pid$|reqasid$|asid$|reqt$|targetid$|slot$|ds_evtid$)/i.test(key)) {
        url.searchParams.delete(key);
      }
    }
    url.hostname = url.hostname.toLocaleLowerCase();
    url.pathname = url.pathname.replace(/\/+$/u, "");
    return `${url.origin}${url.pathname}${url.search}`.toLocaleLowerCase();
  } catch {
    return normalized.toLocaleLowerCase();
  }
}

function getSpotlightRecordMatchKeys(item) {
  const values = Array.isArray(item?.spotlightRecordIds) ? item.spotlightRecordIds : [];
  return [...new Set(values
    .map((value) => toDisplayText(value).trim().toLocaleLowerCase())
    .filter((value) => value && value.length >= 5)
    .map((value) => `record:${value}`))];
}

function getSpotlightTitleMatchScore(left, right) {
  const leftText = normalizeSpotlightSearchText(left);
  const rightText = normalizeSpotlightSearchText(right);
  if (!leftText || !rightText) return 0;
  if (leftText === rightText) return 1;

  const leftTokens = new Set(getSpotlightLocationTokens(leftText));
  const rightTokens = new Set(getSpotlightLocationTokens(rightText));
  if (!leftTokens.size || !rightTokens.size) return 0;
  if (Math.min(leftTokens.size, rightTokens.size) === 1) return 0;

  const overlap = [...leftTokens].filter((token) => rightTokens.has(token)).length;
  if (overlap < 2) return 0;
  const dice = (2 * overlap) / (leftTokens.size + rightTokens.size);
  const containment = overlap / Math.min(leftTokens.size, rightTokens.size);
  return Math.max(dice, containment * 0.9);
}

function getSpotlightCreditIdentity(value) {
  const credit = toDisplayText(value).replace(/^©\s*/u, "");
  const primary = credit.split(/[\/|,;]/u)[0];
  return normalizeSpotlightSearchText(primary);
}

function getSpotlightLocationTokens(value) {
  const ignored = new Set([
    "the", "and", "of", "in", "at", "on", "a", "an", "to", "from",
    "image", "photo", "photograph", "view", "spotlight", "windows",
    "argentina", "argentine", "province", "state", "country",
  ]);
  return normalizeSpotlightSearchText(value)
    .split(/\s+/u)
    .filter((token) => token.length > 2 && !ignored.has(token));
}

function parsePeapixSpotlightPage(html) {
  if (typeof DOMParser === "undefined") return null;
  const documentNode = new DOMParser().parseFromString(String(html || ""), "text/html");
  const pageTitle = toDisplayText(documentNode.querySelector("h1")?.textContent);
  const subtitle = toDisplayText(documentNode.querySelector("h3")?.textContent);
  const paragraphs = [...documentNode.querySelectorAll("main p, article p, p")]
    .map((node) => toDisplayText(node.textContent))
    .filter((text) => text.length > 50 && !/^©/u.test(text));
  const description = [subtitle, ...paragraphs]
    .filter(Boolean)
    .join("\n\n")
    .trim();
  if (!description) return null;
  return { pageTitle, description };
}

function readCachedPeapixSpotlightFeed() {
  try {
    const cached = JSON.parse(localStorage.getItem(PEAPIX_SPOTLIGHT_FEED_CACHE_KEY) || "null");
    if (cached && cached.expiresAt > Date.now() && Array.isArray(cached.items)) {
      return cached.items;
    }
  } catch {
    // Ignore unavailable or expired local cache data.
  }
  return [];
}

async function fetchPeapixSpotlightFeed() {
  const cached = readCachedPeapixSpotlightFeed();
  if (cached.length) return cached;
  if (peapixSpotlightFeedPromise) return peapixSpotlightFeedPromise;
  peapixSpotlightFeedPromise = (async () => {
    const controller = new AbortController();
    const timeoutId = setTimeout(() => controller.abort(), 9000);
    try {
      const params = new URLSearchParams({ n: "500" });
      const response = await fetch(`${PEAPIX_SPOTLIGHT_FEED_URL}?${params.toString()}`, {
        method: "GET",
        headers: { Accept: "application/json" },
        cache: "no-store",
        credentials: "omit",
        signal: controller.signal,
      });
      if (!response.ok) throw new Error(`Spotlight gallery feed returned HTTP ${response.status}.`);
      const payload = await response.json();
      if (!Array.isArray(payload)) throw new Error("Spotlight gallery feed returned an invalid payload.");
      try {
        localStorage.setItem(PEAPIX_SPOTLIGHT_FEED_CACHE_KEY, JSON.stringify({
          expiresAt: Date.now() + PEAPIX_SPOTLIGHT_FEED_CACHE_TTL,
          items: payload,
        }));
      } catch {
        // Continue without persisting the optional gallery cache.
      }
      return payload;
    } finally {
      clearTimeout(timeoutId);
    }
  })().finally(() => {
    peapixSpotlightFeedPromise = null;
  });
  return peapixSpotlightFeedPromise;
}

async function fetchPeapixSpotlightPage(pageUrl) {
  const normalizedUrl = normalizeHttpsUrl(pageUrl);
  if (!normalizedUrl || !/^https:\/\/peapix\.com\/spotlight\//i.test(normalizedUrl)) return null;
  const controller = new AbortController();
  const timeoutId = setTimeout(() => controller.abort(), 7000);
  try {
    const response = await fetch(normalizedUrl, {
      method: "GET",
      headers: { Accept: "text/html" },
      cache: "force-cache",
      credentials: "omit",
      signal: controller.signal,
    });
    if (!response.ok) return null;
    return parsePeapixSpotlightPage(await response.text());
  } catch {
    return null;
  } finally {
    clearTimeout(timeoutId);
  }
}

async function fetchSpotlightGalleryDescription(item, locale) {
  const creditIdentity = getSpotlightCreditIdentity(item.copyright);
  if (!toDisplayText(item.title)) return null;

  try {
    const sourceLanguage = normalizeTranslationLanguageCode(
      isLikelyEnglishSpotlightTitle(item.title, locale) ? "en" : item.titleLanguage || getSpotlightLocaleLanguage(locale),
    );
    let searchableTitle = item.title;
    const translationCache = readSpotlightTranslationCache();
    if (sourceLanguage !== "en") {
      searchableTitle = await translateSpotlightText(item.title, sourceLanguage, "en", translationCache);
      writeSpotlightTranslationCache(translationCache);
    }

    const locationTokens = getSpotlightLocationTokens(searchableTitle);
    if (!locationTokens.length) return null;

    const feedItems = await fetchPeapixSpotlightFeed();
    const candidates = feedItems.map((candidate) => {
      const candidateCredit = getSpotlightCreditIdentity(candidate.copyright);
      const sameCredit = Boolean(creditIdentity && candidateCredit && candidateCredit === creditIdentity);
      const titleScore = getSpotlightTitleMatchScore(searchableTitle, candidate.title);
      const score = sameCredit && titleScore >= 0.35 ? 0.68 + titleScore * 0.32 : titleScore;
      return { candidate, sameCredit, titleScore, score };
    }).filter(({ candidate, sameCredit, score }) =>
      candidate.pageUrl && (sameCredit || score >= 0.76),
    ).sort((a, b) => b.score - a.score).slice(0, 6);

    for (const { candidate, sameCredit, score } of candidates) {
      const page = await fetchPeapixSpotlightPage(candidate.pageUrl);
      if (!page) continue;
      const searchablePage = normalizeSpotlightSearchText(
        `${candidate.title || ""} ${page.pageTitle} ${page.description}`,
      );
      const matchedTokens = locationTokens.filter((token) => searchablePage.includes(token));
      const requiredMatches = locationTokens.length > 1 ? Math.min(2, locationTokens.length) : 1;
      const pageTitleScore = getSpotlightTitleMatchScore(searchableTitle, `${candidate.title || ""} ${page.pageTitle || ""}`);
      if (matchedTokens.length < requiredMatches) continue;
      if (!sameCredit && score < 0.82 && pageTitleScore < 0.78) continue;
      return {
        description: page.description,
        descriptionLanguage: "en",
        descriptionSourceUrl: candidate.pageUrl,
      };
    }
  } catch {
    // No verified gallery match is available for this image.
  }
  return null;
}

async function enrichSpotlightMetadata(item, locale) {
  const isKoreanTarget = getSpotlightLocaleLanguage(locale) === "ko";
  const hasEnglishMicrosoftDescription =
    item.descriptionSource === "english-feed" &&
    hasVisibleSpotlightText(item.description) &&
    !isGenericSpotlightMetadata(item.description);

  // Korean Spotlight records do not reliably carry the detailed description.
  // Always try the gallery when no usable English Microsoft description was
  // matched, even if the Korean feed happened to provide a short visible text.
  if (isKoreanTarget ? hasEnglishMicrosoftDescription : !isGenericSpotlightMetadata(item.description)) {
    return item;
  }

  const gallery = await fetchSpotlightGalleryDescription(item, locale);
  if (!gallery) {
    return item;
  }
  return {
    ...item,
    ...gallery,
    descriptionSource: isKoreanTarget ? "peapix-fallback" : "peapix",
  };
}

function toDisplayText(value) {
  if (typeof value === "string") return value.trim();
  if (typeof value === "number") return String(value);
  return "";
}

function cleanSpotlightDisplayText(value) {
  return toDisplayText(value)
    // Normalize common whitespace entities and remove invisible formatting
    // characters that can make textContent non-empty while rendering nothing.
    .replace(/&(?:nbsp|#0*160|#x0*a0);/gi, " ")
    .replace(/&#(?:8203|8204|8205|65279);|&#x(?:200b|200c|200d|feff);/gi, "")
    .replace(/[\u00a0\u2007\u202f]/gu, " ")
    .replace(/[\u00ad\u200b-\u200d\u2060\ufeff]/gu, "")
    .replace(/[\u0000-\u0008\u000b\u000c\u000e-\u001f\u007f]/gu, "")
    .trim();
}

function hasVisibleSpotlightText(value) {
  const text = cleanSpotlightDisplayText(value);
  return Boolean(text && /[\p{L}\p{N}]/u.test(text));
}

function normalizeMetadataText(value) {
  return cleanSpotlightDisplayText(value).replace(/\s+/g, " ").trim().toLocaleLowerCase();
}

function isGenericSpotlightMetadata(value) {
  const normalized = normalizeMetadataText(value);
  if (!normalized || isSpotlightActionText(value)) return true;
  return [
    "windows spotlight",
    "바탕 화면에서 사진으로 세상을 여행해 보세요. 오늘의 배경 이미지에 대해 자세히 알아보거나 새 배경 이미지를 선택할 수 있습니다.".toLocaleLowerCase(),
    "travel the world with photos on your desktop. learn more about today's background image or choose a new background image.".toLocaleLowerCase(),
    "通过桌面照片畅游世界。详细了解今天的背景图像，或选择新的背景图像。".toLocaleLowerCase(),
    "デスクトップの写真で世界を旅しましょう。今日の背景画像について詳しく確認するか、新しい背景画像を選択できます。".toLocaleLowerCase(),
  ].includes(normalized);
}

function isSpotlightActionText(value) {
  const normalized = normalizeMetadataText(value).normalize("NFKC");
  if (!normalized) return false;
  return (
    /\bright[- ]click\b.*\b(?:learn more|more information|details)\b/i.test(normalized) ||
    /마우스\s*오른쪽.*(?:클릭|누르).*(?:자세히|알아보|더\s*알아)|오른쪽\s*마우스.*(?:클릭|누르).*(?:자세히|알아보|더\s*알아)/u.test(normalized) ||
    /(?:자세히|더\s*알아보려면).*마우스\s*오른쪽.*(?:클릭|누르)/u.test(normalized) ||
    /(?:이\s*)?(?:사진|이미지|배경(?:\s*이미지)?).{0,35}(?:자세히\s*알아보|더\s*알아보|자세한?\s*정보|상세한?\s*정보|더\s*많은\s*정보|새\s*배경)/u.test(normalized) ||
    /(?:자세히\s*알아보|더\s*알아보|자세한?\s*정보|상세한?\s*정보|더\s*많은\s*정보).{0,35}(?:이\s*)?(?:사진|이미지|배경)/u.test(normalized) ||
    /(?:마우스\s*오른쪽|오른쪽\s*마우스).{0,45}(?:클릭|누르).{0,35}(?:자세히|상세|알아보|더\s*알아)/u.test(normalized) ||
    /右键.*(?:了解|查看|获取).*(?:详细信息|更多信息|详情)|右键单击以了解详细信息/u.test(normalized) ||
    /右クリック.*(?:詳細|詳しく|もっと)/u.test(normalized)
  );
}

function parseSpotlightEntry(entry, locale) {
  let item = entry?.item ?? entry;
  if (typeof item === "string") {
    try {
      item = JSON.parse(item);
    } catch {
      return null;
    }
  }

  const ad = item?.ad ?? item;
  const imageAsset = ad?.landscapeImage?.asset;
  const imageUrl = normalizeHttpsUrl(
    typeof imageAsset === "string" ? imageAsset : imageAsset?.url,
  );
  if (!imageUrl) return null;

  const hoverLines = toDisplayText(ad.iconHoverText)
    .split(/\r\n?|\n|\u2028|\u2029/)
    .map((line) => line.trim())
    .filter(Boolean);
  const hoverTitle = hoverLines.find(
    (line) => !/^©/.test(line) && !isGenericSpotlightMetadata(line),
  ) || "";
  const hoverDescription = hoverLines.find(
    (line) => line !== hoverTitle && !/^©/.test(line) && !isGenericSpotlightMetadata(line),
  ) || "";
  const metadataTitleCandidates = [
    ad.title,
    ad.headline,
    ad.imageTitle,
    ad.photoTitle,
    ad.locationName,
  ].map(toDisplayText);
  const metadataTitle = metadataTitleCandidates.find(
    (value) => !isGenericSpotlightMetadata(value),
  ) || "";
  const title = metadataTitle || hoverTitle;
  const titleSource = metadataTitle ? "metadata" : hoverTitle ? "hover" : "unavailable";
  const titleLanguage = isLikelyEnglishSpotlightText(title, locale) ? "en" : getSpotlightLocaleLanguage(locale);
  const descriptionCandidates = [
    ad.description,
    ad.imageDescription,
    ad.longDescription,
    ad.summary,
    ad.caption,
    hoverDescription,
  ].map(toDisplayText);
  const description = descriptionCandidates.find((value) => !isGenericSpotlightMetadata(value)) || "";
  const descriptionLanguage = isLikelyEnglishSpotlightText(description, locale)
    ? "en"
    : getSpotlightLocaleLanguage(locale);
  const copyright =
    (!isGenericSpotlightMetadata(ad.copyright) ? toDisplayText(ad.copyright) : "") ||
    hoverLines.find((line) => /^©/.test(line) && !isGenericSpotlightMetadata(line)) ||
    "";
  const sourceUrl = normalizeHttpsUrl(toDisplayText(ad.ctaUri));
  const assetObject = typeof imageAsset === "object" && imageAsset ? imageAsset : {};
  const recordIds = [
    ad.id,
    ad._id,
    ad.creativeId,
    ad.creativeID,
    ad.assetId,
    ad.imageId,
    ad.landscapeImage?.id,
    ad.landscapeImage?.assetId,
    assetObject.id,
    assetObject.assetId,
    item?.prm?._id,
  ].filter((value) => value !== undefined && value !== null && String(value).trim());

  return {
    imageUrl,
    title,
    titleSource,
    titleLanguage,
    description,
    descriptionLanguage,
    copyright,
    sourceUrl,
    spotlightRecordIds: [...new Set(recordIds.map((value) => String(value)))],
  };
}

function parseSpotlightFeed(payload, locale) {
  const entries = payload?.batchrsp?.items ?? payload?.items ?? [];
  if (!Array.isArray(entries)) return [];
  return entries.map((entry) => parseSpotlightEntry(entry, locale)).filter(Boolean);
}

async function fetchSpotlightFeed(locale, country) {
  const params = new URLSearchParams({
    placement: SPOTLIGHT_PLACEMENT,
    bcnt: "4",
    country,
    locale,
    fmt: "json",
  });
  const requestUrl = `${SPOTLIGHT_FEED_URL}?${params.toString()}`;
  const response = await fetch(requestUrl, {
    method: "GET",
    headers: { Accept: "application/json" },
    cache: "no-store",
    credentials: "omit",
  });
  if (!response.ok) {
    throw new Error(`Windows Spotlight feed returned HTTP ${response.status}.`);
  }
  return parseSpotlightFeed(await response.json(), locale);
}

function createSpotlightMatchIndex(items, keySelector) {
  const index = new Map();
  items.forEach((item) => {
    keySelector(item).forEach((key) => {
      if (!index.has(key)) index.set(key, []);
      index.get(key).push(item);
    });
  });
  return index;
}

function findMatchingFallbackItem(item, fallbackIndexes) {
  const imageKeys = [
    `image:${item.imageUrl}`,
    ...getSpotlightAssetMatchKeys(item.imageUrl),
  ];
  for (const key of imageKeys) {
    const matches = fallbackIndexes.images.get(key) || [];
    if (matches.length === 1) return matches[0];
  }
  const sourceKey = getSpotlightSourceMatchKey(item.sourceUrl);
  if (sourceKey) {
    const sourceMatches = fallbackIndexes.sources.get(sourceKey) || [];
    if (sourceMatches.length === 1) return sourceMatches[0];
  }
  return null;
}

function needsKoreanSpotlightDescriptionFallback(items) {
  // A source marker alone is not enough: a whitespace/zero-width description
  // must never make the next English-feed request look complete.
  return items.some((item) => !(
    item.descriptionSource === "english-feed" &&
    hasVisibleSpotlightText(item.description) &&
    !isGenericSpotlightMetadata(item.description)
  ));
}

function findMatchingSpotlightImageItem(item, imageIndex, sourceIndex, recordIndex) {
  const imageKeys = [
    `image:${item.imageUrl}`,
    ...getSpotlightAssetMatchKeys(item.imageUrl),
  ];
  for (const key of imageKeys) {
    const matches = imageIndex.get(key) || [];
    if (matches.length === 1) return { item: matches[0], method: "이미지 에셋 일치" };
  }
  for (const key of getSpotlightRecordMatchKeys(item)) {
    const matches = recordIndex.get(key) || [];
    if (matches.length === 1) return { item: matches[0], method: "에셋 식별자 일치" };
  }
  // Localized responses can vary query parameters or tracking tokens on the
  // same learn-more page. Compare the canonical destination, not raw URLs.
  const sourceKey = getSpotlightSourceMatchKey(item.sourceUrl);
  if (sourceKey) {
    const sourceMatches = sourceIndex.get(sourceKey) || [];
    if (sourceMatches.length === 1) return { item: sourceMatches[0], method: "원본 상세 링크 일치" };
  }
  return null;
}

async function findMatchingSpotlightTitleItem(item, englishItems, translationCache) {
  const title = toDisplayText(item.title);
  if (!title) return null;
  let englishTitle = title;
  const sourceLanguage = normalizeTranslationLanguageCode(
    isLikelyEnglishSpotlightTitle(title, "ko-KR") ? "en" : item.titleLanguage || "ko",
  );
  if (sourceLanguage !== "en") {
    englishTitle = await translateSpotlightText(title, sourceLanguage, "en", translationCache);
  }
  const sourceCredit = getSpotlightCreditIdentity(item.copyright);
  const candidates = englishItems.map((candidate) => {
    const candidateTitle = toDisplayText(candidate.title);
    const titleScore = getSpotlightTitleMatchScore(englishTitle, candidateTitle);
    const candidateCredit = getSpotlightCreditIdentity(candidate.copyright);
    const sameCredit = Boolean(sourceCredit && candidateCredit && sourceCredit === candidateCredit);
    const score = sameCredit && titleScore >= 0.35
      ? 0.68 + titleScore * 0.32
      : titleScore;
    return { item: candidate, score, titleScore, sameCredit };
  }).filter((entry) => entry.score >= (entry.sameCredit ? 0.68 : 0.76))
    .sort((a, b) => b.score - a.score);

  if (!candidates.length) return null;
  if (candidates.length > 1 && candidates[0].score - candidates[1].score < 0.12) return null;
  return { item: candidates[0].item, method: candidates[0].sameCredit ? "사진작가·제목 대조" : "번역 제목 대조" };
}

async function mergeKoreanSpotlightDescriptions(koreanItems, englishItems, englishLocale) {
  const englishImageIndex = createSpotlightMatchIndex(englishItems, (item) => [
    ...(item.imageUrl ? [`image:${item.imageUrl}`] : []),
    ...getSpotlightAssetMatchKeys(item.imageUrl),
  ]);
  const englishSourceIndex = createSpotlightMatchIndex(
    englishItems,
    (item) => {
      const key = getSpotlightSourceMatchKey(item.sourceUrl);
      return key ? [key] : [];
    },
  );
  const englishRecordIndex = createSpotlightMatchIndex(englishItems, getSpotlightRecordMatchKeys);
  const translationCache = readSpotlightTranslationCache();
  const mergedItems = [];

  for (const item of koreanItems) {
    // Keep an already matched, visible English description.
    if (
      item.descriptionSource === "english-feed" &&
      hasVisibleSpotlightText(item.description) &&
      !isGenericSpotlightMetadata(item.description)
    ) {
      mergedItems.push({ ...item });
      continue;
    }

    let match = findMatchingSpotlightImageItem(
      item, englishImageIndex, englishSourceIndex, englishRecordIndex,
    );
    // A Korean localized feed and its English counterpart do not always expose
    // the same CDN key or destination URL. Use a conservative, unique title
    // match (with photographer credit as an extra signal) as the last join key.
    if (!match) {
      match = await findMatchingSpotlightTitleItem(item, englishItems, translationCache);
    }

    const englishMatch = match?.item;
    const englishDescription = cleanSpotlightDisplayText(englishMatch?.description);
    if (!hasVisibleSpotlightText(englishDescription) || isGenericSpotlightMetadata(englishDescription)) {
      mergedItems.push({
        ...item,
      });
      continue;
    }

    mergedItems.push({
      ...item,
      description: englishDescription,
      descriptionLanguage: "en",
      descriptionSource: "english-feed",
      descriptionSourceLocale: englishLocale,
    });
  }

  writeSpotlightTranslationCache(translationCache);
  return mergedItems;
}

async function fetchKoreanSpotlightDescriptions(items, country) {
  let enrichedItems = items;
  const englishRequestLocales = [...new Set([
    `en-${country}`,
    ...(country === "US" ? [] : ["en-US"]),
  ])];

  for (const englishLocale of englishRequestLocales) {
    if (!needsKoreanSpotlightDescriptionFallback(enrichedItems)) break;
    try {
      // Korean artwork details are not officially localized. Request the same
      // country's feed in English first, then en-US as a metadata fallback.
      const englishItems = await fetchSpotlightFeed(englishLocale, country);
      if (englishItems.length) {
        enrichedItems = await mergeKoreanSpotlightDescriptions(
          enrichedItems,
          englishItems,
          englishLocale,
        );
      }
    } catch {
      // Try the next supported English locale if the current feed is unavailable.
    }
  }

  return enrichedItems;
}

function mergeSpotlightMetadata(localizedItems, fallbackItems) {
  const fallbackIndexes = {
    images: createSpotlightMatchIndex(fallbackItems, (item) => [
      ...(item.imageUrl ? [`image:${item.imageUrl}`] : []),
      ...getSpotlightAssetMatchKeys(item.imageUrl),
    ]),
    sources: createSpotlightMatchIndex(
      fallbackItems,
      (item) => {
        const key = getSpotlightSourceMatchKey(item.sourceUrl);
        return key ? [key] : [];
      },
    ),
  };

  return localizedItems.map((item) => {
    const fallback = findMatchingFallbackItem(item, fallbackIndexes);
    if (!fallback) return item;

    const fallbackTitle = isGenericSpotlightMetadata(fallback.title) ? "" : fallback.title;
    const fallbackDescription = isGenericSpotlightMetadata(fallback.description)
      ? ""
      : fallback.description;
    const currentTitleLanguage = normalizeTranslationLanguageCode(item.titleLanguage);
    const replaceTitle = Boolean(fallbackTitle) && (
      isGenericSpotlightMetadata(item.title) ||
      item.titleSource === "hover" ||
      currentTitleLanguage === "en"
    );
    const replaceDescription = Boolean(fallbackDescription) && (
      isGenericSpotlightMetadata(item.description) ||
      normalizeTranslationLanguageCode(item.descriptionLanguage) === "en"
    );

    const currentCopyright = isGenericSpotlightMetadata(item.copyright)
      ? ""
      : toDisplayText(item.copyright);
    const fallbackCopyright = isGenericSpotlightMetadata(fallback.copyright)
      ? ""
      : toDisplayText(fallback.copyright);

    return {
      ...item,
      title: replaceTitle ? fallbackTitle : item.title,
      titleLanguage: replaceTitle ? fallback.titleLanguage : item.titleLanguage,
      titleSource: replaceTitle ? "fallback" : item.titleSource,
      description: replaceDescription ? fallbackDescription : item.description,
      descriptionLanguage: replaceDescription ? fallback.descriptionLanguage : item.descriptionLanguage,
      copyright: currentCopyright || fallbackCopyright,
      sourceUrl: normalizeHttpsUrl(item.sourceUrl) || normalizeHttpsUrl(fallback.sourceUrl),
    };
  });
}

function readSpotlightTranslationCache() {
  try {
    const value = JSON.parse(localStorage.getItem(SPOTLIGHT_TRANSLATION_CACHE_KEY) || "{}");
    return value && typeof value === "object" && !Array.isArray(value) ? value : {};
  } catch {
    return {};
  }
}

function writeSpotlightTranslationCache(cache) {
  try {
    const entries = Object.entries(cache)
      .filter(([, value]) => typeof value === "string" && hasVisibleSpotlightText(value))
      .slice(-240);
    localStorage.setItem(SPOTLIGHT_TRANSLATION_CACHE_KEY, JSON.stringify(Object.fromEntries(entries)));
  } catch {
    // Keep the current session working if local storage is unavailable.
  }
}

function getUtf8ByteLength(value) {
  return new TextEncoder().encode(value).length;
}

function splitSpotlightTranslationText(value, maxBytes = 420) {
  const text = toDisplayText(value);
  if (!text) return [];
  const sentences = text.match(/[^.!?。！？]+[.!?。！？]*/gu) || [text];
  const chunks = [];
  let current = "";
  for (const sentence of sentences) {
    if (getUtf8ByteLength(sentence) <= maxBytes) {
      if (current && getUtf8ByteLength(current + sentence) > maxBytes) {
        chunks.push(current);
        current = sentence;
      } else {
        current += sentence;
      }
      continue;
    }
    if (current) {
      chunks.push(current);
      current = "";
    }
    const tokens = sentence.match(/\s+|[^\s]+/gu) || [sentence];
    for (const token of tokens) {
      if (current && getUtf8ByteLength(current + token) > maxBytes) {
        chunks.push(current);
        current = "";
      }
      if (getUtf8ByteLength(token) <= maxBytes) {
        current += token;
      } else {
        let fragment = "";
        for (const character of token) {
          if (fragment && getUtf8ByteLength(fragment + character) > maxBytes) {
            chunks.push(fragment);
            fragment = "";
          }
          fragment += character;
        }
        current += fragment;
      }
    }
  }
  if (current) chunks.push(current);
  return chunks;
}

function decodeSpotlightTranslation(value) {
  let text = toDisplayText(value);
  if (text && typeof document !== "undefined") {
    const textarea = document.createElement("textarea");
    textarea.innerHTML = text;
    text = textarea.value;
  }
  return cleanSpotlightDisplayText(text);
}

function normalizeTranslationLanguageCode(language) {
  const normalized = String(language || "en").replace(/_/g, "-");
  if (/^zh(?:-|$)/i.test(normalized)) {
    if (/^(?:zh-TW|zh-HK|zh-MO)$/i.test(normalized)) return "zh-TW";
    return "zh-CN";
  }
  return normalized.split("-")[0].toLocaleLowerCase() || "en";
}

async function translateSpotlightSegment(value, sourceLanguage, targetLanguage, cache) {
  const key = `${sourceLanguage}|${targetLanguage}|${value}`;
  if (typeof cache[key] === "string") {
    const cachedTranslation = decodeSpotlightTranslation(cache[key]);
    // Old cache entries may be empty, whitespace-only, or zero-width. Delete
    // them instead of treating them as a completed translation forever.
    if (
      hasVisibleSpotlightText(cachedTranslation) &&
      normalizeMetadataText(cachedTranslation) !== normalizeMetadataText(value)
    ) {
      return cachedTranslation;
    }
    delete cache[key];
  }
  if ((spotlightTranslationBackoff.get(targetLanguage) || 0) > Date.now()) return value;
  const params = new URLSearchParams({
    q: value,
    langpair: `${sourceLanguage}|${targetLanguage}`,
  });
  const controller = new AbortController();
  const timeoutId = setTimeout(() => controller.abort(), 7000);
  let responseStatus = 0;
  try {
    const response = await fetch(`${SPOTLIGHT_TRANSLATION_URL}?${params.toString()}`, {
      method: "GET",
      headers: { Accept: "application/json" },
      cache: "no-store",
      credentials: "omit",
      signal: controller.signal,
    });
    responseStatus = response.status;
    if (!response.ok) throw new Error(`MyMemory translation returned HTTP ${response.status}.`);
    const payload = await response.json();
    if (Number(payload?.responseStatus) !== 200) {
      throw new Error(toDisplayText(payload?.responseDetails) || "MyMemory translation was unavailable.");
    }
    const translated = decodeSpotlightTranslation(payload?.responseData?.translatedText);
    // Some upstream responses are HTTP-successful but contain no visible text
    // (or merely repeat the source). Never cache those as successful results.
    if (
      !hasVisibleSpotlightText(translated) ||
      normalizeMetadataText(translated) === normalizeMetadataText(value) ||
      /^mymemory\s+(?:warning|error)\b/i.test(translated)
    ) {
      return value;
    }
    cache[key] = translated;
    return translated;
  } catch (error) {
    spotlightTranslationBackoff.set(
      targetLanguage,
      Date.now() + (responseStatus === 429 ? 60 * 60 * 1000 : 5 * 60 * 1000),
    );
    return value;
  } finally {
    clearTimeout(timeoutId);
  }
}

async function translateSpotlightText(value, sourceLanguage, targetLanguage, cache) {
  const text = cleanSpotlightDisplayText(value);
  const source = normalizeTranslationLanguageCode(sourceLanguage);
  const target = normalizeTranslationLanguageCode(targetLanguage);
  if (!hasVisibleSpotlightText(text) || !source || !target || source === target) return text;
  const chunks = splitSpotlightTranslationText(text);
  if (!chunks.length) return text;
  const translatedChunks = [];
  for (const chunk of chunks) {
    translatedChunks.push(await translateSpotlightSegment(chunk, source, target, cache));
  }
  const translatedText = cleanSpotlightDisplayText(translatedChunks.join(""));
  return hasVisibleSpotlightText(translatedText) ? translatedText : text;
}

async function localizeSpotlightMetadata(item, locale) {
  const targetLanguage = getSpotlightTranslationLanguage(locale);
  if (!targetLanguage || targetLanguage === "en") return {
    ...item,
  };
  try {
    const cache = readSpotlightTranslationCache();
    const isKoreanTarget = targetLanguage === "ko";
    // A description tagged as coming from Microsoft's English feed is English
    // even if the original Korean feed guessed its language incorrectly.
    const titleSourceLanguage = isKoreanTarget && isLikelyEnglishSpotlightTitle(item.title, locale)
      ? "en"
      : item.titleLanguage;
    const descriptionSourceLanguage = isKoreanTarget && item.descriptionSource === "english-feed"
      ? "en"
      : item.descriptionLanguage;
    const [title, description] = await Promise.all([
      // Preserve Korean titles, but do not leave a title in English when the
      // Korean feed unexpectedly supplied English metadata.
      translateSpotlightText(item.title, titleSourceLanguage, targetLanguage, cache),
      translateSpotlightText(item.description, descriptionSourceLanguage, targetLanguage, cache),
    ]);
    writeSpotlightTranslationCache(cache);

    const titleWasTranslated =
      normalizeTranslationLanguageCode(titleSourceLanguage) !== targetLanguage &&
      normalizeMetadataText(title) !== normalizeMetadataText(item.title);
    const descriptionWasTranslated =
      normalizeTranslationLanguageCode(descriptionSourceLanguage) !== targetLanguage &&
      hasVisibleSpotlightText(description) &&
      normalizeMetadataText(description) !== normalizeMetadataText(item.description);

    const safeDescription = hasVisibleSpotlightText(description)
      ? cleanSpotlightDisplayText(description)
      : cleanSpotlightDisplayText(item.description);

    return {
      ...item,
      title,
      titleLanguage: titleWasTranslated ? targetLanguage : titleSourceLanguage,
      description: safeDescription,
      descriptionLanguage: descriptionWasTranslated ? targetLanguage : descriptionSourceLanguage,
    };
  } catch {
    return item;
  }
}

async function requestSpotlightItems() {
  if (spotlightFetchPromise) return spotlightFetchPromise;

  spotlightFetchPromise = (async () => {
    const locale = getSpotlightRequestLocale();
    const country = getSpotlightCountry(locale);
    let receivedItems = [];

    try {
      receivedItems = await fetchSpotlightFeed(locale, country);
    } catch {
      // Use the cached localized feed or fall back to the English feed below.
    }

    if (!receivedItems.length) {
      const cachedItems = readCachedSpotlightItems(locale, country);
      if (cachedItems.length) {
        receivedItems = cachedItems;
      }
    }

    if (getSpotlightLocaleLanguage(locale) === "ko") {
      // Always request English artwork details for Korean items: the Korean feed
      // may contain a placeholder or a non-detailed description even when non-empty.
      if (receivedItems.length) {
        receivedItems = await fetchKoreanSpotlightDescriptions(receivedItems, country);
      } else {
        // If the localized feed itself is unavailable, use English records as a
        // complete fallback. The localization stage translates English titles
        // and descriptions to Korean while leaving photographer credits intact.
        const englishRequestLocales = [...new Set([
          `en-${country}`,
          ...(country === "US" ? [] : ["en-US"]),
        ])];
        for (const englishLocale of englishRequestLocales) {
          try {
            const englishItems = await fetchSpotlightFeed(englishLocale, country);
            if (!englishItems.length) {
              continue;
            }
            receivedItems = englishItems.map((item) => ({
              ...item,
              titleLanguage: item.titleLanguage || "en",
              descriptionLanguage: "en",
              descriptionSource: "english-feed",
              descriptionSourceLocale: englishLocale,
            }));
            break;
          } catch {
            // Try the next available feed locale.
          }
        }
      }
    } else {
      for (const fallbackLocale of getSpotlightMetadataFallbackLocales(locale, country)) {
        if (receivedItems.length && !needsSpotlightMetadataFallback(receivedItems)) break;

        try {
          const fallbackItems = await fetchSpotlightFeed(fallbackLocale, country);
          if (!fallbackItems.length) continue;

          if (!receivedItems.length) {
            // Keep the requested country while sourcing metadata from a supported language feed.
            receivedItems = fallbackItems;
          } else {
            receivedItems = mergeSpotlightMetadata(receivedItems, fallbackItems);
          }
        } catch {
          // Continue to the next supported metadata feed.
        }
      }
    }

    if (!receivedItems.length) {
      receivedItems = readCachedSpotlightItems(locale, country);
    }

    spotlightItems = receivedItems;
    spotlightItemIndex = 0;
    if (receivedItems.length) writeCachedSpotlightItems(locale, country, receivedItems);
    return spotlightItems;
  })().finally(() => {
    spotlightFetchPromise = null;
  });
  return spotlightFetchPromise;
}

async function getNextSpotlightItem() {
  // On startup, use the previously saved feed before waiting for a live request.
  // This lets the first wallpaper image appear as soon as its image file loads.
  if (spotlightItemIndex >= spotlightItems.length && !startupSpotlightCacheChecked) {
    startupSpotlightCacheChecked = true;
    const locale = getSpotlightRequestLocale();
    const country = getSpotlightCountry(locale);
    const cachedItems = readCachedSpotlightItems(locale, country);
    if (cachedItems.length) {
      spotlightItems = cachedItems;
      spotlightItemIndex = 0;
    }
  }

  if (spotlightItemIndex >= spotlightItems.length) {
    await requestSpotlightItems();
  }
  if (spotlightItemIndex >= spotlightItems.length) return null;
  const item = spotlightItems[spotlightItemIndex];
  spotlightItemIndex += 1;
  return item;
}

function initializeBackgroundLayers(backgroundLayer) {
  backgroundLayerA = backgroundLayer.querySelector(".bg-layer-1");
  backgroundLayerB = backgroundLayer.querySelector(".bg-layer-2");

  if (!backgroundLayerA || !backgroundLayerB) {
    backgroundLayer.innerHTML = "";
    backgroundLayerA = document.createElement("div");
    backgroundLayerB = document.createElement("div");
    backgroundLayerA.className = "bg-sub-layer bg-layer-1 is-startup-wallpaper";
    backgroundLayerB.className = "bg-sub-layer bg-layer-2";
    backgroundLayerA.style.backgroundImage = `url("${new URL("../img/startup.jpg", import.meta.url).href}")`;
    backgroundLayerA.style.opacity = "1";
    backgroundLayerB.style.opacity = "0";
    backgroundLayer.append(backgroundLayerA, backgroundLayerB);
    activeBgIndex = 0;
    hasDisplayedSpotlightImage = navigator.onLine !== false;
  }
}

function updateSpotlightInformation(item) {
  const title = document.getElementById("spotlightImageTitle");
  const description = document.getElementById("spotlightImageDescription");
  const copyright = document.getElementById("spotlightImageCopyright");
  const source = document.getElementById("spotlightImageSource");

  if (title) title.textContent = item.title || getUILocalizedText("Image title unavailable");
  if (description) {
    const visibleDescription = cleanSpotlightDisplayText(item.description);
    const hasDescription = hasVisibleSpotlightText(visibleDescription);
    description.textContent = hasDescription ? visibleDescription : "";
    description.hidden = !hasDescription;
    description.classList.remove("is-unavailable");
  }
  if (copyright) {
    copyright.textContent = item.copyright || getUILocalizedText("Photo credit unavailable");
  }
  if (source) {
    const sourceUrl = normalizeHttpsUrl(item.sourceUrl) || normalizeHttpsUrl(item.descriptionSourceUrl);
    if (sourceUrl) {
      source.href = sourceUrl;
      source.hidden = false;
    } else {
      source.removeAttribute("href");
      source.hidden = true;
    }
    source.textContent = getUILocalizedText("Learn more about this image");
  }
}

function showSpotlightInformationUnavailable() {
  const title = document.getElementById("spotlightImageTitle");
  const description = document.getElementById("spotlightImageDescription");
  const copyright = document.getElementById("spotlightImageCopyright");
  const source = document.getElementById("spotlightImageSource");
  if (title) title.textContent = getUILocalizedText("Image information is unavailable.");
  if (description) {
    description.textContent = "";
    description.hidden = true;
    description.classList.remove("is-unavailable");
  }
  if (copyright) copyright.textContent = "";
  if (source) source.hidden = true;
}

function showSpotlightOfflineBackground() {
  // Offline mode keeps the bundled startup wallpaper visible instead of
  // clearing both layers to black. It also becomes the outgoing layer when
  // the first online Spotlight image arrives after reconnecting.
  const startupImageUrl = new URL("../img/startup.jpg", import.meta.url).href;

  if (backgroundLayerA) {
    backgroundLayerA.classList.add("is-startup-wallpaper");
    backgroundLayerA.style.transition = "none";
    backgroundLayerA.style.backgroundImage = `url("${startupImageUrl}")`;
    backgroundLayerA.style.opacity = "1";
  }
  if (backgroundLayerB) {
    backgroundLayerB.classList.remove("is-startup-wallpaper");
    backgroundLayerB.style.transition = "none";
    backgroundLayerB.style.opacity = "0";
    backgroundLayerB.style.backgroundImage = "none";
  }
  // Apply the local image immediately, without animating through black.
  if (backgroundLayerA) void backgroundLayerA.offsetWidth;
  if (backgroundLayerA) backgroundLayerA.style.removeProperty("transition");
  if (backgroundLayerB) backgroundLayerB.style.removeProperty("transition");

  activeBgIndex = 0;
  // Treat the local image as the currently displayed layer so that the next
  // online Spotlight image crossfades onto layer B instead of appearing abruptly.
  hasDisplayedSpotlightImage = true;
  hasReceivedOnlineSpotlightImage = false;
  startupImageChangeGuardUntil = 0;
  showSpotlightInformationUnavailable();
}

async function loadNextSpotlightImage() {
  if (imageChangeInProgress) return;
  if (navigator.onLine === false) {
    const backgroundLayer = document.getElementById("bgImageLayer");
    if (backgroundLayer) initializeBackgroundLayers(backgroundLayer);
    showSpotlightOfflineBackground();
    return;
  }

  imageChangeInProgress = true;
  const requestId = ++spotlightImageRequestId;

  try {
    const backgroundLayer = document.getElementById("bgImageLayer");
    if (!backgroundLayer) return;
    initializeBackgroundLayers(backgroundLayer);

    const item = await getNextSpotlightItem();
    if (!item) {
      // No feed item is available (including a failed internet request): keep
      // the bundled wallpaper as the safe visual fallback.
      showSpotlightOfflineBackground();
      return;
    }

    const locale = getSpotlightRequestLocale();
    // Image display must not wait for gallery lookups or text translation.
    // Those details are refreshed after the image is already on screen.
    const localizedItemPromise = enrichSpotlightMetadata(item, locale)
      .then((enrichedItem) => localizeSpotlightMetadata(enrichedItem, locale));

    const image = new Image();
    const loaded = await new Promise((resolve) => {
      image.onload = () => resolve(true);
      image.onerror = () => resolve(false);
      image.src = item.imageUrl;
    });

    if (navigator.onLine === false) {
      showSpotlightOfflineBackground();
      return;
    }
    if (!loaded) {
      // Keep the previous image visible if a single feed image is unavailable.
      showSpotlightInformationUnavailable();
      return;
    }

    const firstImage = !hasDisplayedSpotlightImage;
    const nextIndex = firstImage ? 0 : (activeBgIndex === 0 ? 1 : 0);
    const currentLayer = firstImage
      ? null
      : (activeBgIndex === 0 ? backgroundLayerA : backgroundLayerB);
    const nextLayer = nextIndex === 0 ? backgroundLayerA : backgroundLayerB;

    nextLayer.classList.remove("is-startup-wallpaper");
    nextLayer.style.backgroundImage = `url("${image.src}")`;
    if (firstImage) {
      // Do not fade the very first online image in from the black base layer.
      // Subsequent images continue to crossfade A <-> B.
      nextLayer.style.transition = "none";
      nextLayer.style.opacity = "1";
      void nextLayer.offsetWidth;
      nextLayer.style.removeProperty("transition");
    } else {
      nextLayer.style.opacity = "1";
      if (currentLayer) currentLayer.style.opacity = "0";
    }

    activeBgIndex = nextIndex;
    hasDisplayedSpotlightImage = true;
    if (!hasReceivedOnlineSpotlightImage) {
      hasReceivedOnlineSpotlightImage = true;
      startupImageChangeGuardUntil = Date.now() + STARTUP_IMAGE_CHANGE_GUARD_MS;
    }
    updateSpotlightInformation(item);

    localizedItemPromise
      .then((localizedItem) => {
        if (
          requestId === spotlightImageRequestId &&
          hasDisplayedSpotlightImage &&
          navigator.onLine !== false
        ) {
          updateSpotlightInformation(localizedItem);
        }
      })
      .catch(() => {
        // Image display is independent from optional metadata enrichment.
      });
  } catch {
    // If the feed cannot be reached, fall back to the bundled startup image.
    showSpotlightOfflineBackground();
  } finally {
    imageChangeInProgress = false;
    if (reloadSpotlightAfterCurrentImage) {
      reloadSpotlightAfterCurrentImage = false;
      void loadNextSpotlightImage();
    }
  }
}

function initializeSpotlightInfoControl() {
  const control = document.getElementById("spotlightInfoControl");
  const trigger = document.getElementById("spotlightInfoTrigger");
  const panel = document.getElementById("spotlightInfoPanel");
  if (!control || !trigger || !panel) return;

  const setOpen = (open, dismissed = false) => {
    control.classList.toggle("is-open", open);
    control.classList.toggle("is-dismissed", dismissed);
    trigger.setAttribute("aria-expanded", String(open));
    panel.setAttribute("aria-hidden", String(!open));
  };

  control.addEventListener("pointerenter", () => {
    if (!control.classList.contains("is-dismissed")) setOpen(true);
  });
  control.addEventListener("pointerleave", () => {
    setOpen(false);
    control.classList.remove("is-dismissed");
  });
  trigger.addEventListener("focus", () => setOpen(true));
  control.addEventListener("focusout", (event) => {
    if (!control.contains(event.relatedTarget) && !control.matches(":hover")) {
      setOpen(false);
    }
  });
  trigger.addEventListener("click", () => {
    const isOpen = trigger.getAttribute("aria-expanded") === "true";
    setOpen(!isOpen, isOpen);
  });
  document.addEventListener("pointerdown", (event) => {
    if (!control.contains(event.target)) setOpen(false);
  });
  document.addEventListener("keydown", (event) => {
    if (event.key === "Escape" && trigger.getAttribute("aria-expanded") === "true") {
      setOpen(false, true);
      trigger.focus();
    }
  });
}

function showStartupPlaceholder() {
  if (!backgroundLayerA || navigator.onLine === false) return;

  // Keep a bundled image visible from the first paint while the online feed loads.
  // The first real Spotlight image is placed on layer B and crossfades from this layer.
  const placeholderUrl = new URL("../img/startup.jpg", import.meta.url).href;
  backgroundLayerA.classList.add("is-startup-wallpaper");
  backgroundLayerA.style.backgroundImage = `url("${placeholderUrl}")`;
  backgroundLayerA.style.transition = "none";
  backgroundLayerA.style.opacity = "1";
  if (backgroundLayerB) {
    backgroundLayerB.style.backgroundImage = "none";
    backgroundLayerB.style.opacity = "0";
  }
  void backgroundLayerA.offsetWidth;
  backgroundLayerA.style.removeProperty("transition");
  activeBgIndex = 0;
  hasDisplayedSpotlightImage = true;
}

function triggerImageChange() {
  if (ignoreInitialVerseImageChange) {
    ignoreInitialVerseImageChange = false;
    return;
  }
  if (Date.now() < startupImageChangeGuardUntil) return;
  void loadNextSpotlightImage();
}

document.documentElement.classList.add("spotlight");

const backgroundLayer = document.getElementById("bgImageLayer");
if (backgroundLayer) {
  backgroundLayer.style.display = "block";
  initializeBackgroundLayers(backgroundLayer);
  if (navigator.onLine === false) {
    showSpotlightOfflineBackground();
  } else {
    showStartupPlaceholder();
    void loadNextSpotlightImage();
  }
}

const overlay = document.getElementById("bgOverlay");
if (overlay) overlay.style.display = "block";

initializeSpotlightInfoControl();
window.addEventListener("offline", () => {
  showSpotlightOfflineBackground();
});
window.addEventListener("online", () => {
  // Restore a local image immediately while the online Spotlight feed resumes.
  showStartupPlaceholder();
  if (imageChangeInProgress) {
    reloadSpotlightAfterCurrentImage = true;
    return;
  }
  void loadNextSpotlightImage();
});
window.addEventListener("spotlight-ui-language-change", () => {
  spotlightItems = [];
  spotlightItemIndex = 0;
  startupSpotlightCacheChecked = false;
  if (imageChangeInProgress) {
    reloadSpotlightAfterCurrentImage = true;
    return;
  }
  void loadNextSpotlightImage();
});
setContent.startBibleVerseCycle(triggerImageChange);
