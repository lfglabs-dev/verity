const DEFAULT_SUPPORTED_TYPES = [
  "text/html",
  "text/markdown",
  "text/plain",
  "application/json",
] as const;

type SupportedType = (typeof DEFAULT_SUPPORTED_TYPES)[number];

type AcceptedType = {
  type: string;
  q: number;
  index: number;
};

function parseAccept(acceptHeader: string | null): AcceptedType[] {
  if (!acceptHeader) {
    return [];
  }

  return acceptHeader
    .split(",")
    .map((part, index) => {
      const [rawType, ...params] = part.trim().split(";");
      const type = rawType.toLowerCase();
      let q = 1;

      for (const param of params) {
        const [key, value] = param.trim().split("=");
        if (key === "q") {
          const parsed = Number.parseFloat(value);
          q = Number.isFinite(parsed) ? parsed : 0;
        }
      }

      return { type, q, index };
    })
    .filter(({ type, q }) => Boolean(type) && q > 0);
}

function matchSpecificity(accepted: string, supported: string): number {
  if (accepted === supported) {
    return 2;
  }

  const [acceptedType, acceptedSubtype] = accepted.split("/");
  const [supportedType] = supported.split("/");

  if (accepted === "*/*") {
    return 0;
  }

  if (acceptedSubtype === "*" && acceptedType === supportedType) {
    return 1;
  }

  return -1;
}

export function negotiateContentType(
  acceptHeader: string | null,
  supportedTypes: readonly SupportedType[] = DEFAULT_SUPPORTED_TYPES
): SupportedType {
  const acceptedTypes = parseAccept(acceptHeader);

  if (acceptedTypes.length === 0) {
    return "text/html";
  }

  let best: {
    type: SupportedType;
    q: number;
    specificity: number;
    index: number;
  } | null = null;

  for (const accepted of acceptedTypes) {
    for (const supported of supportedTypes) {
      const specificity = matchSpecificity(accepted.type, supported);
      if (specificity < 0) {
        continue;
      }

      const candidate = {
        type: supported,
        q: accepted.q,
        specificity,
        index: accepted.index,
      };

      if (
        !best ||
        candidate.q > best.q ||
        (candidate.q === best.q && candidate.specificity > best.specificity) ||
        (candidate.q === best.q &&
          candidate.specificity === best.specificity &&
          candidate.index < best.index)
      ) {
        best = candidate;
      }
    }
  }

  return best?.type ?? "text/html";
}
