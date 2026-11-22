import { parseHTML } from "linkedom";
import { McpServer, ResourceTemplate } from "@modelcontextprotocol/sdk/server/mcp.js";
import { fileURLToPath } from "node:url";
import { RootsListChangedNotificationSchema } from "@modelcontextprotocol/sdk/types.js";
import { lstat, mkdir, readFile, readdir, realpath, stat, writeFile } from "node:fs/promises";
import path from "node:path";
import { get, tokenize } from "@tonaljs/chord";
import { fromSemitones } from "@tonaljs/interval";
import { majorKey, minorKey } from "@tonaljs/key";
import { chroma, enharmonic, pitchClass, simplify, transpose } from "@tonaljs/note";
import { z } from "zod";
import { marked } from "marked";
import { createServer } from "node:http";
import { StdioServerTransport } from "@modelcontextprotocol/sdk/server/stdio.js";
import { StreamableHTTPServerTransport } from "@modelcontextprotocol/sdk/server/streamableHttp.js";
//#region src/editor/scripts/node-dom-shim.ts
/**
* A minimal browser global environment for running the Open Lyric core in
* Node — the VS Code extension's `worker_threads` worker and the
* `open-lyric-mcp` server process.
*
* The core was written for the page: importing `shared.ts` resolves element
* refs against `document`, checks `instanceof HTMLElement`, and reads
* `localStorage`-backed preferences. None of that matters for validating or
* rendering a song, but it has to *load*, and the string renderers parse HTML
* through `DOMParser`. A linkedom document gives those imports something to
* look at. Install it only in a process or thread the Open Lyric code owns —
* never in a shared host (such as VS Code's extension host), where a global
* `window`/`document` would mislead every other extension's environment checks.
*
* Import this module before any core module (ES module evaluation order).
*/
var MemoryStorage = class {
	#items = /* @__PURE__ */ new Map();
	get length() {
		return this.#items.size;
	}
	key(index) {
		return Array.from(this.#items.keys())[index] ?? null;
	}
	getItem(key) {
		return this.#items.has(key) ? this.#items.get(key) : null;
	}
	setItem(key, value) {
		this.#items.set(String(key), String(value));
	}
	removeItem(key) {
		this.#items.delete(key);
	}
	clear() {
		this.#items.clear();
	}
};
/**
* The DOM classes copied from the linkedom window onto `globalThis` — what the
* core reaches for by global name (`instanceof HTMLElement`, `new DOMParser`,
* `instanceof HTMLAnchorElement` …). Names linkedom does not provide are
* skipped.
*/
var DOM_GLOBAL_NAMES = [
	"Node",
	"Element",
	"Attr",
	"CharacterData",
	"Comment",
	"DocumentFragment",
	"ShadowRoot",
	"Text",
	"NodeList",
	"HTMLElement",
	"HTMLAnchorElement",
	"HTMLAudioElement",
	"HTMLBRElement",
	"HTMLButtonElement",
	"HTMLCanvasElement",
	"HTMLDetailsElement",
	"HTMLDivElement",
	"HTMLFormElement",
	"HTMLHeadingElement",
	"HTMLIFrameElement",
	"HTMLImageElement",
	"HTMLInputElement",
	"HTMLLabelElement",
	"HTMLLIElement",
	"HTMLLinkElement",
	"HTMLOListElement",
	"HTMLOptionElement",
	"HTMLParagraphElement",
	"HTMLPreElement",
	"HTMLScriptElement",
	"HTMLSelectElement",
	"HTMLSlotElement",
	"HTMLSourceElement",
	"HTMLSpanElement",
	"HTMLStyleElement",
	"HTMLTableElement",
	"HTMLTemplateElement",
	"HTMLTextAreaElement",
	"HTMLUListElement",
	"HTMLVideoElement",
	"SVGElement",
	"Image",
	"MutationObserver",
	"CustomEvent",
	"Event",
	"EventTarget",
	"InputEvent"
];
var FULL_HTML_DOCUMENT_RE = /^\s*(?:<!doctype[^>]*>\s*)?<html[\s>]/i;
/**
* linkedom's `DOMParser` builds a document only from a whole HTML page: given
* a fragment (`<p>hi</p>`), `documentElement` is the `<p>` and `body` throws.
* Browsers wrap a fragment in `<html><head></head><body>`, and the core's
* sanitizer (`doc.body.innerHTML`) relies on that — so wrap it here too.
*/
function createFragmentTolerantDomParser(LinkedomDomParser) {
	return class DOMParser extends LinkedomDomParser {
		parseFromString(markup, mimeType) {
			const source = String(markup ?? "");
			return super.parseFromString(mimeType === "text/html" && !FULL_HTML_DOCUMENT_RE.test(source) ? `<!doctype html><html><head></head><body>${source}</body></html>` : source, mimeType);
		}
	};
}
var TEXT_NODE = 3;
var PROCESSING_INSTRUCTION_NODE = 7;
var COMMENT_NODE = 8;
function isCharacterData(node) {
	return node.nodeType === TEXT_NODE || node.nodeType === COMMENT_NODE || node.nodeType === PROCESSING_INSTRUCTION_NODE;
}
function getNodeLength(node) {
	return isCharacterData(node) ? String(node.data ?? "").length : node.childNodes.length;
}
function getNodeIndex(node) {
	return Array.prototype.indexOf.call(node.parentNode?.childNodes ?? [], node);
}
/** Child indexes from the root down to `node`. */
function getNodePath(node) {
	const path = [];
	for (let current = node; current.parentNode; current = current.parentNode) path.unshift(getNodeIndex(current));
	return path;
}
function isInclusiveAncestor(ancestor, node) {
	for (let current = node; current; current = current.parentNode) if (current === ancestor) return true;
	return false;
}
/**
* Order two boundary points. A boundary point `(node, offset)` sorts as its
* node's index path followed by the offset — lexicographically, a prefix
* first — which is exactly the DOM's boundary-point order.
*/
function compareBoundaryPoints(nodeA, offsetA, nodeB, offsetB) {
	const a = [...getNodePath(nodeA), offsetA];
	const b = [...getNodePath(nodeB), offsetB];
	for (let index = 0; index < Math.min(a.length, b.length); index += 1) if (a[index] !== b[index]) return a[index] < b[index] ? -1 : 1;
	return a.length === b.length ? 0 : a.length < b.length ? -1 : 1;
}
/**
* The slice of `Range` the core uses headless — boundary setters and
* `cloneContents()`, after the DOM standard's "clone the contents of a range"
* algorithm. linkedom's own `Range` does not implement them; the lyric
* renderer (`createChordedLyricSegments`) cuts each line at its chord
* placeholders with one, splitting any formatting element that spans a cut.
*/
var ShimRange = class ShimRange {
	startContainer;
	startOffset = 0;
	endContainer;
	endOffset = 0;
	constructor(documentNode) {
		this.startContainer = documentNode;
		this.endContainer = documentNode;
	}
	get collapsed() {
		return this.startContainer === this.endContainer && this.startOffset === this.endOffset;
	}
	setStart(node, offset) {
		this.startContainer = node;
		this.startOffset = offset;
		if (compareBoundaryPoints(node, offset, this.endContainer, this.endOffset) > 0) this.setEnd(node, offset);
	}
	setEnd(node, offset) {
		this.endContainer = node;
		this.endOffset = offset;
		if (compareBoundaryPoints(node, offset, this.startContainer, this.startOffset) < 0) {
			this.startContainer = node;
			this.startOffset = offset;
		}
	}
	setStartBefore(node) {
		this.setStart(node.parentNode, getNodeIndex(node));
	}
	setStartAfter(node) {
		this.setStart(node.parentNode, getNodeIndex(node) + 1);
	}
	setEndBefore(node) {
		this.setEnd(node.parentNode, getNodeIndex(node));
	}
	setEndAfter(node) {
		this.setEnd(node.parentNode, getNodeIndex(node) + 1);
	}
	selectNodeContents(node) {
		this.startContainer = node;
		this.startOffset = 0;
		this.endContainer = node;
		this.endOffset = getNodeLength(node);
	}
	collapse(toStart = false) {
		if (toStart) {
			this.endContainer = this.startContainer;
			this.endOffset = this.startOffset;
		} else {
			this.startContainer = this.endContainer;
			this.startOffset = this.endOffset;
		}
	}
	#isContained(node) {
		return compareBoundaryPoints(node, 0, this.startContainer, this.startOffset) > 0 && compareBoundaryPoints(node, getNodeLength(node), this.endContainer, this.endOffset) < 0;
	}
	#isPartiallyContained(node) {
		return isInclusiveAncestor(node, this.startContainer) !== isInclusiveAncestor(node, this.endContainer);
	}
	cloneContents() {
		const fragment = (this.startContainer.ownerDocument ?? this.startContainer).createDocumentFragment();
		const { startContainer, startOffset, endContainer, endOffset } = this;
		if (this.collapsed) return fragment;
		if (startContainer === endContainer && isCharacterData(startContainer)) {
			const clone = startContainer.cloneNode();
			clone.data = String(startContainer.data ?? "").slice(startOffset, endOffset);
			fragment.appendChild(clone);
			return fragment;
		}
		let commonAncestor = startContainer;
		while (!isInclusiveAncestor(commonAncestor, endContainer)) commonAncestor = commonAncestor.parentNode;
		const children = Array.from(commonAncestor.childNodes);
		const firstPartial = isInclusiveAncestor(startContainer, endContainer) ? null : children.find((child) => this.#isPartiallyContained(child)) ?? null;
		const lastPartial = isInclusiveAncestor(endContainer, startContainer) ? null : [...children].reverse().find((child) => this.#isPartiallyContained(child)) ?? null;
		if (firstPartial && isCharacterData(firstPartial)) {
			const clone = startContainer.cloneNode();
			clone.data = String(startContainer.data ?? "").slice(startOffset);
			fragment.appendChild(clone);
		} else if (firstPartial) {
			const clone = firstPartial.cloneNode(false);
			const subrange = new ShimRange(startContainer);
			subrange.setStart(startContainer, startOffset);
			subrange.setEnd(firstPartial, getNodeLength(firstPartial));
			clone.appendChild(subrange.cloneContents());
			fragment.appendChild(clone);
		}
		children.filter((child) => this.#isContained(child)).forEach((child) => {
			fragment.appendChild(child.cloneNode(true));
		});
		if (lastPartial && isCharacterData(lastPartial)) {
			const clone = endContainer.cloneNode();
			clone.data = String(endContainer.data ?? "").slice(0, endOffset);
			fragment.appendChild(clone);
		} else if (lastPartial) {
			const clone = lastPartial.cloneNode(false);
			const subrange = new ShimRange(lastPartial);
			subrange.setStart(lastPartial, 0);
			subrange.setEnd(endContainer, endOffset);
			clone.appendChild(subrange.cloneContents());
			fragment.appendChild(clone);
		}
		return fragment;
	}
};
function installDomShim() {
	const globals = globalThis;
	if (globals.__openLyricDomShimInstalled) return;
	if (typeof globals.document !== "undefined" && typeof globals.DOMParser === "function") {
		globals.__openLyricDomShimInstalled = true;
		return;
	}
	const browserWindow = parseHTML("<!doctype html><html><head></head><body></body></html>");
	const definitions = {
		window: browserWindow,
		self: browserWindow,
		document: browserWindow.document,
		localStorage: new MemoryStorage(),
		sessionStorage: new MemoryStorage(),
		matchMedia: () => ({
			matches: false,
			media: "",
			addEventListener() {},
			removeEventListener() {},
			addListener() {},
			removeListener() {}
		}),
		requestAnimationFrame: (callback) => setTimeout(() => callback(Date.now()), 16),
		cancelAnimationFrame: (handle) => clearTimeout(handle)
	};
	DOM_GLOBAL_NAMES.forEach((name) => {
		if (browserWindow[name] !== void 0) definitions[name] = browserWindow[name];
	});
	const browserDocument = browserWindow.document;
	if (typeof browserDocument.createRange?.().setStart !== "function") browserDocument.createRange = () => new ShimRange(browserDocument);
	if (typeof browserWindow.DOMParser === "function") definitions.DOMParser = createFragmentTolerantDomParser(browserWindow.DOMParser);
	Object.entries(definitions).forEach(([name, value]) => {
		Object.defineProperty(globalThis, name, {
			configurable: true,
			enumerable: false,
			value,
			writable: true
		});
	});
	Object.entries(definitions).forEach(([name, value]) => {
		if (name !== "window" && name !== "self") browserWindow[name] ??= value;
	});
	if (definitions.DOMParser) browserWindow.DOMParser = definitions.DOMParser;
	globals.__openLyricDomShimInstalled = true;
}
installDomShim();
//#endregion
//#region src/mcp-common/client-roots.ts
/**
* The client's `roots/list` as file paths, for {@link FileAccess}: `null` when
* the client does not offer roots (or does not answer in time — a stateless
* HTTP request cannot carry a server-to-client request), so the configured
* roots apply. Cached until the client says the list changed.
*/
function createClientRootsLister(server, { timeoutMs = 3e3 } = {}) {
	let cached = null;
	server.server.setNotificationHandler(RootsListChangedNotificationSchema, () => {
		cached = null;
	});
	const fetchRoots = async () => {
		if (!server.server.getClientCapabilities()?.roots) return null;
		let timer;
		try {
			const result = await Promise.race([server.server.listRoots(), new Promise((resolve) => {
				timer = setTimeout(() => resolve(null), timeoutMs);
			})]);
			if (!result) return null;
			const paths = result.roots.filter((root) => root.uri.startsWith("file:")).map((root) => fileURLToPath(root.uri));
			return paths.length ? paths : null;
		} catch {
			return null;
		} finally {
			clearTimeout(timer);
		}
	};
	return () => {
		cached ??= fetchRoots().then((roots) => {
			if (!roots) cached = null;
			return roots;
		});
		return cached;
	};
}
//#endregion
//#region src/mcp-common/file-access.ts
var FileAccessError = class extends Error {};
var SKIPPED_DIRECTORY_NAMES = /* @__PURE__ */ new Set([
	"node_modules",
	".git",
	"dist"
]);
function isInside(child, root) {
	const relative = path.relative(root, child);
	return relative === "" || !relative.startsWith(`..${path.sep}`) && relative !== ".." && !path.isAbsolute(relative);
}
function toPath(input) {
	const value = String(input ?? "").trim();
	if (!value) throw new FileAccessError("A path is required.");
	return value.startsWith("file:") ? fileURLToPath(value) : value;
}
async function realpathOrNull(target) {
	try {
		return await realpath(target);
	} catch {
		return null;
	}
}
function hasAllowedExtension(filePath, extensions) {
	const lower = filePath.toLowerCase();
	return extensions.some((extension) => lower.endsWith(extension.toLowerCase()));
}
var FileAccess = class {
	#configuredRoots;
	#cwd;
	#listClientRoots;
	readOnly;
	constructor({ configuredRoots = [], readOnly = false, cwd = process.cwd(), listClientRoots } = {}) {
		this.#cwd = cwd;
		this.#configuredRoots = configuredRoots.map((root) => path.resolve(cwd, toPath(root)));
		this.#listClientRoots = listClientRoots;
		this.readOnly = readOnly;
	}
	/** The roots in effect right now, real paths, deduplicated. */
	async getRoots() {
		let clientRoots = [];
		try {
			clientRoots = await this.#listClientRoots?.() ?? [];
		} catch {
			clientRoots = [];
		}
		const candidates = [...clientRoots, ...this.#configuredRoots];
		const roots = [];
		for (const candidate of candidates.length ? candidates : [this.#cwd]) {
			const real = await realpathOrNull(path.resolve(this.#cwd, candidate));
			if (real && !roots.includes(real)) roots.push(real);
		}
		return roots;
	}
	async #resolve(input) {
		const roots = await this.getRoots();
		if (!roots.length) throw new FileAccessError("No file roots are available — start the server with --root <dir>.");
		const candidate = toPath(input);
		return {
			absolute: path.isAbsolute(candidate) ? path.normalize(candidate) : path.resolve(roots[0], candidate),
			roots
		};
	}
	#assertInsideRoots(realTarget, roots, input) {
		if (!roots.some((root) => isInside(realTarget, root))) throw new FileAccessError(`"${input}" is outside the allowed roots (${roots.join(", ")}).`);
	}
	/** The real path of an existing file inside the roots. */
	async resolveForRead(input) {
		const { absolute, roots } = await this.#resolve(input);
		const real = await realpathOrNull(absolute);
		if (!real) throw new FileAccessError(`File not found: ${absolute}`);
		this.#assertInsideRoots(real, roots, input);
		return real;
	}
	/** Where a write to `input` lands, once checked against the roots. */
	async resolveForWrite(input, extensions) {
		if (this.readOnly) throw new FileAccessError("The server is read-only; writing is disabled.");
		const { absolute, roots } = await this.#resolve(input);
		if (extensions.length && !hasAllowedExtension(absolute, extensions)) throw new FileAccessError(`Refusing to write "${absolute}": the file must end in ${extensions.join(", ")}.`);
		let existing = path.dirname(absolute);
		const missingSegments = [path.basename(absolute)];
		while (!await realpathOrNull(existing)) {
			const parent = path.dirname(existing);
			if (parent === existing) throw new FileAccessError(`Cannot resolve a parent folder of ${absolute}.`);
			missingSegments.unshift(path.basename(existing));
			existing = parent;
		}
		const realParent = await realpathOrNull(existing);
		const target = path.join(realParent, ...missingSegments);
		this.#assertInsideRoots(target, roots, input);
		try {
			const stats = await lstat(target);
			if (stats.isSymbolicLink()) {
				const realTarget = await realpathOrNull(target);
				if (!realTarget) throw new FileAccessError(`Refusing to write through the dangling link ${target}.`);
				this.#assertInsideRoots(realTarget, roots, input);
				return realTarget;
			}
			if (stats.isDirectory()) throw new FileAccessError(`${target} is a folder, not a file.`);
		} catch (error) {
			if (error instanceof FileAccessError) throw error;
		}
		return target;
	}
	/**
	* A UTF-8 file inside the roots. With `maxBytes`, a larger file is refused
	* before it is read.
	*/
	async readText(input, { maxBytes } = {}) {
		const resolved = await this.resolveForRead(input);
		if (maxBytes !== void 0) {
			const { size } = await stat(resolved);
			if (size > maxBytes) throw new FileAccessError(`${resolved} is ${size} bytes; the limit is ${maxBytes}.`);
		}
		return {
			path: resolved,
			text: await readFile(resolved, "utf8")
		};
	}
	async writeFile(input, data, extensions) {
		const resolved = await this.resolveForWrite(input, extensions);
		await mkdir(path.dirname(resolved), { recursive: true });
		await writeFile(resolved, data);
		return {
			path: resolved,
			bytes: typeof data === "string" ? Buffer.byteLength(data, "utf8") : data.byteLength
		};
	}
	/**
	* Files under `directory` (default: every root) whose names end in one of
	* `extensions`, skipping dot-folders, `node_modules`, `.git` and `dist`.
	*/
	async listFiles({ directory, extensions, recursive = true, limit = 500 }) {
		const starts = directory ? [await this.resolveForRead(directory)] : await this.getRoots();
		const files = [];
		let truncated = false;
		const walk = async (folder) => {
			if (truncated) return;
			let entries;
			try {
				entries = await readdir(folder, { withFileTypes: true });
			} catch {
				return;
			}
			entries.sort((a, b) => a.name.localeCompare(b.name));
			for (const entry of entries) {
				if (truncated) return;
				const entryPath = path.join(folder, entry.name);
				if (entry.isDirectory()) {
					if (recursive && !entry.name.startsWith(".") && !SKIPPED_DIRECTORY_NAMES.has(entry.name)) await walk(entryPath);
					continue;
				}
				if (entry.isFile() && hasAllowedExtension(entry.name, extensions)) {
					if (files.length >= limit) {
						truncated = true;
						return;
					}
					files.push(entryPath);
				}
			}
		};
		for (const start of starts) await walk(start);
		return {
			files,
			truncated
		};
	}
};
//#endregion
//#region src/mcp-common/results.ts
/**
* Tool result helpers shared by the Open Lyric MCP servers.
*
* A tool that declares an `outputSchema` returns its data twice: as
* `structuredContent` (what a client validates and programs against) and as a
* text block holding a one-line summary plus the same JSON, for clients that
* only read `content`.
*/
function structuredResult(data, summary = "") {
	const json = JSON.stringify(data, null, 2);
	return {
		content: [{
			type: "text",
			text: summary ? `${summary}\n\n${json}` : json
		}],
		structuredContent: data
	};
}
function errorMessage(error) {
	if (error instanceof Error) return error.message;
	return String(error);
}
function errorResult(error) {
	return {
		isError: true,
		content: [{
			type: "text",
			text: errorMessage(error)
		}]
	};
}
/**
* Run a tool body, turning a thrown error into an `isError` result — the MCP
* way to tell the model its call failed (bad input, a path outside the roots),
* as opposed to a protocol error.
*/
async function runTool(body) {
	try {
		return await body();
	} catch (error) {
		return errorResult(error);
	}
}
//#endregion
//#region src/editor/scripts/config-locales.ts
/**
* Every locale tag an `ol:Config` `Locales` field may list — the Windows LCID
* tag set, kept in this repository as `locale.txt`.
*
* Data only, and complete on purpose: naming every tag is what keeps the core
* script-neutral. `km-KH` sits here as one row of 229, not as a language the
* core knows about — a Khmer document still earns its keyboard, fonts, and
* spellcheck from the km-KH plugin, never from this list.
*
* Order is the source file's, which is also the order the Monaco `Locales`
* completion offers the tags in.
*
* The transcript plugin keeps its own near-identical picker list
* (`BASE_TRANSCRIPT_LOCALE_SUGGESTIONS`) on purpose — that one is a UI menu a
* language plugin extends through the registry, this one is the notation's
* closed value set.
*/
var CONFIG_LOCALE_VALUES = [
	"arc",
	"af-ZA",
	"am-ET",
	"ar-AE",
	"ar-BH",
	"ar-DZ",
	"ar-EG",
	"ar-IQ",
	"ar-JO",
	"ar-KW",
	"ar-LB",
	"ar-LY",
	"ar-MA",
	"arn-CL",
	"ar-OM",
	"ar-QA",
	"ar-SA",
	"ar-SD",
	"ar-SY",
	"ar-TN",
	"ar-YE",
	"as-IN",
	"az-az",
	"az-Cyrl-AZ",
	"az-Latn-AZ",
	"ba-RU",
	"be-BY",
	"bg-BG",
	"bn-BD",
	"bn-IN",
	"bo-CN",
	"br-FR",
	"bs-Cyrl-BA",
	"bs-Latn-BA",
	"ca-ES",
	"co-FR",
	"cs-CZ",
	"cy-GB",
	"da-DK",
	"de-AT",
	"de-CH",
	"de-DE",
	"de-LI",
	"de-LU",
	"dsb-DE",
	"dv-MV",
	"el-CY",
	"el-GR",
	"en-029",
	"en-AU",
	"en-BZ",
	"en-CA",
	"en-cb",
	"en-GB",
	"en-IE",
	"en-IN",
	"en-JM",
	"en-MT",
	"en-MY",
	"en-NZ",
	"en-PH",
	"en-SG",
	"en-TT",
	"en-US",
	"en-ZA",
	"en-ZW",
	"es-AR",
	"es-BO",
	"es-CL",
	"es-CO",
	"es-CR",
	"es-DO",
	"es-EC",
	"es-ES",
	"es-GT",
	"es-HN",
	"es-MX",
	"es-NI",
	"es-PA",
	"es-PE",
	"es-PR",
	"es-PY",
	"es-SV",
	"es-US",
	"es-UY",
	"es-VE",
	"et-EE",
	"eu-ES",
	"fa-IR",
	"fi-FI",
	"fil-PH",
	"fo-FO",
	"fr-BE",
	"fr-CA",
	"fr-CH",
	"fr-FR",
	"fr-LU",
	"fr-MC",
	"fy-NL",
	"ga-IE",
	"gd-GB",
	"gd-ie",
	"gl-ES",
	"gsw-FR",
	"gu-IN",
	"ha-Latn-NG",
	"he-IL",
	"hi-IN",
	"hr-BA",
	"hr-HR",
	"hsb-DE",
	"hu-HU",
	"hy-AM",
	"id-ID",
	"ig-NG",
	"ii-CN",
	"in-ID",
	"is-IS",
	"it-CH",
	"it-IT",
	"iu-Cans-CA",
	"iu-Latn-CA",
	"iw-IL",
	"ja-JP",
	"ka-GE",
	"kk-KZ",
	"kl-GL",
	"km-KH",
	"kn-IN",
	"kok-IN",
	"ko-KR",
	"ky-KG",
	"lb-LU",
	"lo-LA",
	"lt-LT",
	"lv-LV",
	"mi-NZ",
	"mk-MK",
	"ml-IN",
	"mn-MN",
	"mn-Mong-CN",
	"moh-CA",
	"mr-IN",
	"ms-BN",
	"ms-MY",
	"mt-MT",
	"nb-NO",
	"ne-NP",
	"nl-BE",
	"nl-NL",
	"nn-NO",
	"no-no",
	"nso-ZA",
	"oc-FR",
	"or-IN",
	"pa-IN",
	"pl-PL",
	"prs-AF",
	"ps-AF",
	"pt-BR",
	"pt-PT",
	"qut-GT",
	"quz-BO",
	"quz-EC",
	"quz-PE",
	"rm-CH",
	"ro-mo",
	"ro-RO",
	"ru-mo",
	"ru-RU",
	"rw-RW",
	"sah-RU",
	"sa-IN",
	"se-FI",
	"se-NO",
	"se-SE",
	"si-LK",
	"sk-SK",
	"sl-SI",
	"sma-NO",
	"sma-SE",
	"smj-NO",
	"smj-SE",
	"smn-FI",
	"sms-FI",
	"sq-AL",
	"sr-BA",
	"sr-CS",
	"sr-Cyrl-BA",
	"sr-Cyrl-CS",
	"sr-Cyrl-ME",
	"sr-Cyrl-RS",
	"sr-Latn-BA",
	"sr-Latn-CS",
	"sr-Latn-ME",
	"sr-Latn-RS",
	"sr-ME",
	"sr-RS",
	"sr-sp",
	"sv-FI",
	"sv-SE",
	"sw-KE",
	"syr-SY",
	"ta-IN",
	"te-IN",
	"tg-Cyrl-TJ",
	"th-TH",
	"tk-TM",
	"tlh-QS",
	"tn-ZA",
	"tr-TR",
	"tt-RU",
	"tzm-Latn-DZ",
	"ug-CN",
	"uk-UA",
	"ur-PK",
	"uz-Cyrl-UZ",
	"uz-Latn-UZ",
	"uz-uz",
	"vi-VN",
	"wo-SN",
	"xh-ZA",
	"yo-NG",
	"zh-CN",
	"zh-HK",
	"zh-MO",
	"zh-SG",
	"zh-TW",
	"zu-ZA"
];
//#endregion
//#region src/plugins/OpenLyric/examples/example1.ol.md?raw
var example1_ol_default = "# Extended Worship Build\n\nUse this example to test an extended worship flow with multiple bridges, instrumentals, repeat counts, and a final chorus.\n\n```ol:Config\n- Title: Extended Worship Build\n- Artist: Open Lyric Team\n- Copyright: 2026 Open Lyric\n- Key: E\n- Tempo: 70bpm\n- Time: 4/4\n- Strumming Patterns:\n	// Slow rolling pulse\n	d--u-- | d-u-d-\n	// Lift on the chorus\n	ddu--u | d-d-du\n- Structure: IV1x2Cx2V2x2Cx4IS1B1x6IS2B2x4B1x6IS1Cx4FO\n```\n\n```ol:Verse 1\n// Keys only on the first pass; band joins on the repeat\nTo the earth You humbly came,  The King of kings to take my place\nOn the cross You died for me,  Your mercy made a way for grace\n```\n\n```ol:Verse 2\nWhen I look upon Your face,  I see compassion without end\nThe Name of Jesus Christ our King,  My faithful healer and my friend\n```\n\n```ol:Intro\n||: C#m | B/D# | E | E :|| E |\n```\n\n```ol:Chorus\n|[C#m]Jesus, You carried my [B/D#]burden\n|[E]far beyond the reach of night\n// Drums build from here\n|[C#m]Jesus, You opened my [B/D#]future\n|[E]with resurrection light\n```\n\n```ol:Bridge 1\n// Six times through: add one layer each pass\n|[E]I am healed now      |[C#m]I am standing free\n    You have called me out  From all my slavery\n|[A]Every chain is broken |[B]Faith is rising here\n    Hearts awake in wonder  Love has drawn us near\n```\n\n```ol:Instrumental 1\n// Guitar takes the chorus melody\n{c: Gtr Solo } | E | C#m | A | B | (2x)\n```\n\n```ol:Instrumental 2\n{c: Keys + Gtr Solo } | E | C#m | A | B | (4x)\n```\n\n```ol:Bridge 2\n|[E]Oh....     |[C#m]Oh....     |[A]Oh....     |[B]Oh....\n```\n\n```ol:Outro\n{c: Piano + pads } | E | C#m | A | B |\n```\n\n```ol:Final-Chorus\n// Up a whole step from E to F#m\n|[F#m]Jesus, You carried my [C#]burden\n|[B]far beyond the reach of night\n|[F#m]Jesus, You opened my [C#]future\n|[B]with resurrection light\n// Hold the last chord, then straight into the outro\n```\n";
//#endregion
//#region src/editor/assets/examples/editor-welcome-note.md?raw
var editor_welcome_note_default = "# Team Welcome Notes\n\n## Welcome\n\nWelcome to the editor workspace.\nintendedspellcheck\n\nThis page is for writing notes, adjusting formatting, and organizing content\nbefore converting it into anything else.\n\n## Checklist\n\n- Confirm the event title\n- Add speaker notes\n- Share the final draft\n\n> Plain markdown notes of any kind live comfortably in the editor page.\n";
//#endregion
//#region src/editor/html/markup-fragments.ts
/**
* Look up a shell element by its `data-ol-ref` handle.
*
* The fragments carry no `id` at all — a page-global id in reusable markup
* makes a second instance illegal on arrival, so every JS handle is an
* instance-agnostic attribute instead. `root` is what scopes a lookup to one
* instance; it defaults to the document for the wrap-phase single-instance
* app. (The ids the fragments still *reference* — `for`, `aria-controls`,
* `aria-labelledby` — are generated per install by `linkFragmentIds()`.)
*/
function queryRef(name, root = document) {
	return root.querySelector(`[data-ol-ref="${name}"]`);
}
//#endregion
//#region src/editor/scripts/page-config.ts
var EDITOR_ONLY_SHELL_MODE = "editor-only";
var FULL_EDITOR_SHELL_MODE = "full";
function getEditorShellMode() {
	if (typeof document === "undefined") return FULL_EDITOR_SHELL_MODE;
	return document.documentElement?.dataset.editorShell === "editor-only" ? EDITOR_ONLY_SHELL_MODE : FULL_EDITOR_SHELL_MODE;
}
function getDefaultPanelVisibilityForCurrentPage() {
	const hasEditorPanel = queryRef("editorPanel") instanceof HTMLElement;
	const hasPreviewPanel = queryRef("previewPanel") instanceof HTMLElement;
	const hasOpenLyricPanel = queryRef("openLyricPanel") instanceof HTMLElement;
	if (getEditorShellMode() === "editor-only") return {
		editorVisible: hasEditorPanel,
		previewVisible: false,
		openLyricVisible: false
	};
	if (hasOpenLyricPanel) return {
		editorVisible: false,
		previewVisible: false,
		openLyricVisible: true
	};
	if (hasPreviewPanel) return {
		editorVisible: false,
		previewVisible: true,
		openLyricVisible: false
	};
	return {
		editorVisible: hasEditorPanel,
		previewVisible: false,
		openLyricVisible: false
	};
}
//#endregion
//#region src/editor/scripts/editor-only-draft-examples.ts
var DEFAULT_EDITOR_ONLY_DRAFT_EXAMPLE = {
	id: "editor-welcome-note",
	fileName: "editor-welcome-note.md",
	title: "Welcome Note",
	description: "Plain markdown welcome notes for the editor-only page.",
	content: editor_welcome_note_default,
	editorShellModes: [EDITOR_ONLY_SHELL_MODE]
};
//#endregion
//#region src/editor/scripts/default-draft-example.ts
var DEFAULT_FULL_DRAFT_EXAMPLE = {
	id: "open_lyric_ol_editor:example1",
	fileName: "example1.ol.md",
	title: "Extended Worship Build",
	description: "Extended worship flow with multiple bridges, instrumentals, repeat counts, and a final chorus.",
	content: example1_ol_default,
	editorShellModes: [FULL_EDITOR_SHELL_MODE]
};
function getDefaultDraftExample() {
	return getEditorShellMode() === "editor-only" ? DEFAULT_EDITOR_ONLY_DRAFT_EXAMPLE : DEFAULT_FULL_DRAFT_EXAMPLE;
}
getDefaultDraftExample();
//#endregion
//#region src/editor/scripts/editor-metadata.ts
var OPEN_LYRIC_EDITOR_INFO = Object.freeze({
	name: "Open Lyric",
	version: "0.1.9-dev"
});
function getCurrentEditorShell() {
	return String(globalThis.document?.documentElement?.dataset?.editorShell ?? "").trim();
}
function getEditorDisplayName() {
	return getCurrentEditorShell() === "editor-only" ? "" : OPEN_LYRIC_EDITOR_INFO.name;
}
function getCurrentBrowserLocationUrl() {
	return String(globalThis.location?.href ?? "").trim();
}
function formatEditorVersion(version = OPEN_LYRIC_EDITOR_INFO.version) {
	const normalizedVersion = String(version ?? "").trim();
	if (!normalizedVersion) return "";
	return normalizedVersion.startsWith("v") ? normalizedVersion : `v${normalizedVersion}`;
}
function getEditorSignature() {
	const editorName = getEditorDisplayName();
	const versionLabel = formatEditorVersion();
	if (editorName && versionLabel) return `${editorName} ${versionLabel}`;
	if (editorName) return editorName;
	return versionLabel ? `Editor ${versionLabel}` : "Editor";
}
function getEditorVersionBadgeText() {
	const versionLabel = formatEditorVersion();
	return versionLabel ? `Editor ${versionLabel}` : "Editor";
}
function getEditorMetadataTitle() {
	return [getEditorSignature(), getCurrentBrowserLocationUrl()].filter(Boolean).join(" · ");
}
//#endregion
//#region src/plugins/OpenLyric/preview/controller/pptx/export-fonts.ts
/** A big-endian `uint16`/`uint32` of `bytes` at `offset`. */
var readUint16 = (bytes, offset) => bytes[offset] << 8 | bytes[offset + 1];
var readUint32 = (bytes, offset) => (bytes[offset] << 24 >>> 0) + (bytes[offset + 1] << 16) + (bytes[offset + 2] << 8) + bytes[offset + 3];
/**
* Whether `bytes` is a TrueType font (glyph outlines a Word document can
* embed) whose maker lets it travel inside a document: its `OS/2` table's
* `fsType` neither restricts embedding (bit 1) nor allows bitmaps only
* (bit 9). A font with no `OS/2` table states no restriction.
*/
function isEmbeddableTrueTypeFont(bytes) {
	if (!(bytes instanceof Uint8Array) || bytes.length < 12) return false;
	const version = readUint32(bytes, 0);
	if (version !== 65536 && version !== 1953658213) return false;
	const tableCount = readUint16(bytes, 4);
	if (bytes.length < 12 + tableCount * 16) return false;
	for (let index = 0; index < tableCount; index++) {
		const record = 12 + index * 16;
		if (String.fromCharCode(...bytes.subarray(record, record + 4)) !== "OS/2") continue;
		const offset = readUint32(bytes, record + 8);
		if (offset + 10 > bytes.length) return false;
		const fsType = readUint16(bytes, offset + 8);
		return (fsType & 2) === 0 && (fsType & 512) === 0;
	}
	return true;
}
//#endregion
//#region src/editor/scripts/editor-plugin-registry.ts
var defaultPluginRuntime = {
	keyboardSpecifications: /* @__PURE__ */ new Map(),
	listeners: /* @__PURE__ */ new Set(),
	nextPluginId: 1,
	openLyricSpecifications: /* @__PURE__ */ new Map(),
	registeredPlugins: /* @__PURE__ */ new Set(),
	spellcheckSpecifications: /* @__PURE__ */ new Map(),
	transcriptSpecifications: /* @__PURE__ */ new Map()
};
var runtimeHost = globalThis;
var pluginRuntime = runtimeHost.__openLyricEditorPluginRuntime || (runtimeHost.__openLyricEditorPluginRuntime = defaultPluginRuntime);
function getRegisteredSpellcheckSpecifications() {
	return Array.from(pluginRuntime.spellcheckSpecifications.values());
}
//#endregion
//#region src/editor/scripts/shared.ts
function escapeRegex(value) {
	return value.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}
/** Test a plugin-supplied pattern without inheriting its `lastIndex`. */
function testPattern(pattern, value) {
	pattern.lastIndex = 0;
	return pattern.test(value);
}
var LANGUAGE_ID = "markdown-ol";
var DEFAULT_THEME = "dark";
var LEADING_SPACE_LIKE_RE = /^[\s\u200B]+/u;
var TRAILING_SPACE_LIKE_RE = /[\s\u200B]+$/u;
var SPACE_LIKE_SEQUENCE_RE = /[\s\u200B]+/gu;
var FORM_SECTION_NAMES = [
	"Final-Chorus",
	"Pre-Chorus",
	"Post-Chorus",
	"Instrumental",
	"Interlude",
	"Breakdown",
	"Refrain",
	"Bridge",
	"Chorus",
	"Verse",
	"Intro",
	"Note",
	"Tag",
	"Turnaround",
	"Vamp",
	"Solo",
	"Outro"
];
var LYRIC_SECTION_NAMES = [
	"Final-Chorus",
	"Pre-Chorus",
	"Post-Chorus",
	"Refrain",
	"Bridge",
	"Chorus",
	"Verse",
	"Note",
	"Tag",
	"Turnaround",
	"Outro"
];
var INSTRUMENTAL_SECTION_NAMES = ["Instrumental", "Interlude"];
var FREE_TEXT_SECTION_NAMES = [
	"Breakdown",
	"Vamp",
	"Solo"
];
var NUMBERED_SECTION_NAMES = [
	"Verse",
	"Note",
	"Pre-Chorus",
	"Chorus",
	"Post-Chorus",
	"Refrain",
	"Bridge",
	"Instrumental",
	"Interlude",
	"Turnaround",
	"Breakdown",
	"Solo",
	"Tag"
];
var CONFIG_FIELD_NAMES$1 = [
	"Title",
	"Subtitle",
	"Description",
	"Artist",
	"Copyright",
	"Locales",
	"Key",
	"Tempo",
	"Time",
	"Theme",
	"Structure",
	"Genre",
	"Style",
	"Keywords",
	"Year",
	"Melody",
	"Attachments",
	"Strumming Patterns"
];
var CONFIG_FIELD_ALIASES = { "Strumming Pattern": "Strumming Patterns" };
var CONFIG_FIELD_MATCH_NAMES$1 = Array.from(/* @__PURE__ */ new Set([...CONFIG_FIELD_NAMES$1, ...Object.keys(CONFIG_FIELD_ALIASES)]));
var CONFIG_REQUIRED_FIELD_NAMES$1 = ["Title", "Structure"];
var CONFIG_MULTILINE_FIELD_NAMES$1 = [
	"Description",
	"Attachments",
	"Strumming Patterns"
];
var CONFIG_KEY_VALUES = [
	"C",
	"Db",
	"D",
	"Eb",
	"E",
	"F",
	"F#",
	"Gb",
	"G",
	"Ab",
	"A",
	"Bb",
	"B",
	"Am",
	"Bbm",
	"Bm",
	"Cm",
	"C#m",
	"Dm",
	"D#m",
	"Ebm",
	"Em",
	"Fm",
	"F#m",
	"Gm",
	"G#m"
];
var CONFIG_ENUM_FIELD_VALUES$1 = {
	Key: CONFIG_KEY_VALUES,
	Time: [
		"4/4",
		"2/2",
		"2/4",
		"3/4",
		"3/8",
		"6/8",
		"9/8",
		"12/8"
	]
};
var CONFIG_PATTERN_FIELD_VALUES$1 = {
	Tempo: /^[1-9]\d*bpm$/,
	Year: /^[1-9]\d{3}$/
};
/** What a value failing its {@link CONFIG_PATTERN_FIELD_VALUES} pattern is told. */
var CONFIG_PATTERN_FIELD_MESSAGES$1 = {
	Tempo: "Tempo must be a whole number of beats per minute then bpm, such as 76bpm.",
	Year: "Year must be a four-digit year, such as 2024."
};
var CONFIG_LOCALE_VALUE_SET = new Set(CONFIG_LOCALE_VALUES);
var CONFIG_LOCALE_VALUES_BY_LOWERCASE = new Map(CONFIG_LOCALE_VALUES.map((localeTag) => [localeTag.toLowerCase(), localeTag]));
var STRUMMING_PATTERN_STEP_CHARACTERS = /* @__PURE__ */ new Set([
	"d",
	"D",
	"v",
	"V",
	"u",
	"U",
	"^",
	"x",
	"X",
	"1",
	"*",
	"+",
	"-",
	"_",
	".",
	"0"
]);
var STRUMMING_PATTERN_SEPARATOR_CHARACTERS = /* @__PURE__ */ new Set([
	"|",
	" ",
	"	"
]);
var STRUMMING_PATTERN_DASH_LIKE_RE = /[\u2010\u2011\u2012\u2013\u2014\u2015\u2212\uFE58\uFE63\uFF0D]/g;
var STRUMMING_PATTERN_BAR_LIKE_RE = /[\u2223\u2758\uFF5C]/g;
var STRUMMING_PATTERN_WHITESPACE_RE = /[\u00A0\u1680\u2000-\u200A\u202F\u205F\u3000]/g;
var STRUMMING_PATTERN_SPACE_LIKE_RE = /[\u00A0\u1680\u2000-\u200B\u202F\u205F\u3000]/g;
/**
* True when the text carries a registered language's invisible word separator
* AND is written in that language's script — i.e. those zero-width characters
* are real word boundaries, not stray invisible junk to strip.
*/
function shouldAllowInvisibleWordSeparators(value, contextValue = value) {
	const source = String(value ?? "");
	const contextText = String(contextValue ?? source);
	return getRegisteredSpellcheckSpecifications().some((specification) => {
		const separator = specification.wordSeparator;
		return typeof separator === "string" && separator && source.includes(separator) && specification.baseLetterPattern instanceof RegExp && testPattern(specification.baseLetterPattern, contextText);
	});
}
/**
* Repair whitespace typed between words of a script that separates them
* invisibly, rewriting each run to the language's own separator.
*
* The rule comes entirely from the plugin — `wordSeparatorPattern` (whose
* first capture group is the character to keep) plus `wordSeparator`. Used by
* paste handling and the Format action; a no-op with no such language
* registered.
*/
function normalizeWordSeparators(value, options = {}) {
	const source = String(value ?? "");
	if (!source) return source;
	const rewrites = getRegisteredSpellcheckSpecifications().filter((specification) => specification.wordSeparatorPattern instanceof RegExp && typeof specification.wordSeparator === "string" && specification.wordSeparator);
	if (!rewrites.length) return source;
	const leadingContext = String(options.leadingText ?? "").slice(-1);
	const trailingContext = String(options.trailingText ?? "").charAt(0);
	const contextValue = `${leadingContext}${source}${trailingContext}`;
	const normalizedValue = rewrites.reduce((text, { wordSeparatorPattern, wordSeparator }) => {
		wordSeparatorPattern.lastIndex = 0;
		return text.replace(wordSeparatorPattern, `$1${wordSeparator}`);
	}, contextValue);
	const endIndex = normalizedValue.length - trailingContext.length;
	return normalizedValue.slice(leadingContext.length, endIndex);
}
function isSpaceLikeCharacter(character, allowZeroWidthSpace = true) {
	return Boolean(character) && (allowZeroWidthSpace && character === "​" || /\s/u.test(character));
}
function getLeadingSpaceLikeLength(value, allowZeroWidthSpace = true) {
	return String(value ?? "").match(allowZeroWidthSpace ? /^[\s\u200B]*/u : /^\s*/u)?.[0].length || 0;
}
function trimSpaceLikeStart(value, allowZeroWidthSpace = true) {
	return String(value ?? "").replace(allowZeroWidthSpace ? LEADING_SPACE_LIKE_RE : /^\s+/u, "");
}
function trimSpaceLikeEnd(value, allowZeroWidthSpace = true) {
	return String(value ?? "").replace(allowZeroWidthSpace ? TRAILING_SPACE_LIKE_RE : /\s+$/u, "");
}
function trimSpaceLikeText(value, allowZeroWidthSpace = true) {
	return trimSpaceLikeEnd(trimSpaceLikeStart(value, allowZeroWidthSpace), allowZeroWidthSpace);
}
function collapseSpaceLikeText(value, replacement = " ", allowZeroWidthSpace = true) {
	return String(value ?? "").replace(allowZeroWidthSpace ? SPACE_LIKE_SEQUENCE_RE : /\s+/gu, replacement);
}
function normalizeConfigFieldName(fieldName) {
	const trimmedFieldName = String(fieldName ?? "").trim();
	return CONFIG_FIELD_ALIASES[trimmedFieldName] || trimmedFieldName;
}
/**
* Split a `Locales` value into its comma-separated tags, each with the offsets
* it occupies inside the value text.
*
* The offsets are what make this shared: validation turns them into marker
* columns, and the Monaco completion turns them into a replace range. Empty
* segments (a stray or trailing comma) are kept rather than dropped — an empty
* entry is a thing to report, so it must survive the parse.
*/
function parseConfigLocaleEntries(value, allowZeroWidthSpace = true) {
	const text = String(value ?? "");
	const entries = [];
	let segmentStartOffset = 0;
	for (let index = 0; index <= text.length; index += 1) {
		if (index < text.length && text[index] !== ",") continue;
		const segment = text.slice(segmentStartOffset, index);
		const leadingLength = getLeadingSpaceLikeLength(segment, allowZeroWidthSpace);
		const trimmedSegment = trimSpaceLikeText(segment, allowZeroWidthSpace);
		const startOffset = segmentStartOffset + leadingLength;
		entries.push({
			text: trimmedSegment,
			startOffset,
			endOffset: startOffset + trimmedSegment.length
		});
		segmentStartOffset = index + 1;
	}
	return entries;
}
function isSupportedConfigLocale(value) {
	return CONFIG_LOCALE_VALUE_SET.has(String(value ?? ""));
}
/**
* The supported tag that only differs from `value` in case — `''` when the tag
* is unknown however it is cased. Locale tags are written `en-US`, so a typed
* `en-us` is a casing slip worth naming in the message rather than a different
* value.
*/
function findCanonicalConfigLocale(value) {
	const normalizedValue = String(value ?? "").toLowerCase();
	return CONFIG_LOCALE_VALUES_BY_LOWERCASE.get(normalizedValue) || "";
}
function normalizeStrummingPatternValue(value, allowZeroWidthSpace = true) {
	return String(value ?? "").replace(STRUMMING_PATTERN_DASH_LIKE_RE, "-").replace(STRUMMING_PATTERN_BAR_LIKE_RE, "|").replace(allowZeroWidthSpace ? STRUMMING_PATTERN_SPACE_LIKE_RE : STRUMMING_PATTERN_WHITESPACE_RE, " ");
}
function isValidStrummingPatternValue(value, allowZeroWidthSpace = true) {
	const normalizedValue = normalizeStrummingPatternValue(value, allowZeroWidthSpace);
	let hasStepCharacter = false;
	for (const character of normalizedValue) {
		if (STRUMMING_PATTERN_STEP_CHARACTERS.has(character)) {
			hasStepCharacter = true;
			continue;
		}
		if (STRUMMING_PATTERN_SEPARATOR_CHARACTERS.has(character)) continue;
		return false;
	}
	return hasStepCharacter;
}
var MAJOR_CHORD_ROOTS = [
	"C",
	"Db",
	"D",
	"Eb",
	"E",
	"F",
	"F# / Gb",
	"G",
	"Ab",
	"A",
	"Bb",
	"B"
];
var MINOR_CHORD_ROOTS = [
	"A",
	"Bb",
	"B",
	"C",
	"C#",
	"D",
	"D# / Eb",
	"E",
	"F",
	"F#",
	"G",
	"G#"
];
var CHORD_EXTENSION_LABELS = [
	["2", "2nds"],
	["4", "4ths"],
	["5", "5ths"],
	["6", "6ths"],
	["7", "7ths"],
	["9", "9ths"],
	["11", "11ths"],
	["13", "13ths"]
];
function appendChordSuffix(displayRoot, suffix) {
	return displayRoot.split("/").map((variant) => `${variant.trim()}${suffix}`).join(" / ");
}
function createChordKeyGroup(name, roots, suffix) {
	return {
		name,
		keys: roots.map((root) => appendChordSuffix(root, suffix))
	};
}
var CHORD_KEY_GROUPS = [
	{
		name: "Major Keys",
		keys: MAJOR_CHORD_ROOTS
	},
	createChordKeyGroup("Minor Keys", MINOR_CHORD_ROOTS, "m"),
	...CHORD_EXTENSION_LABELS.flatMap(([suffix, label]) => [
		createChordKeyGroup(`Keys with ${label}`, MAJOR_CHORD_ROOTS, suffix),
		createChordKeyGroup(`Major Keys with ${label}`, MAJOR_CHORD_ROOTS, `maj${suffix}`),
		createChordKeyGroup(`Minor Keys with ${label}`, MINOR_CHORD_ROOTS, `m${suffix}`)
	])
];
var CONFIG_HEADER_RE = /^Config$/;
var INTRO_HEADER_RE = /^Intro$/;
var INSTRUMENTAL_HEADER_RE = new RegExp(`^(${INSTRUMENTAL_SECTION_NAMES.map(escapeRegex).join("|")})(?:\\s+([1-9]\\d*))?$`);
var LYRIC_HEADER_RE = new RegExp(`^(${LYRIC_SECTION_NAMES.map(escapeRegex).join("|")})(?:\\s+([1-9]\\d*))?$`);
var FREE_TEXT_HEADER_RE = new RegExp(`^(${FREE_TEXT_SECTION_NAMES.map(escapeRegex).join("|")})(?:\\s+([1-9]\\d*))?$`);
var CHORD_EXTENSION_SOURCE = String.raw`(?:2|4|5|6|7|9|11|13)`;
var CHORD_QUALITY_SOURCE = String.raw`(?:maj|min|m|dim|aug)`;
var CHORD_DECORATION_SOURCE = String.raw`(?:${CHORD_QUALITY_SOURCE}(?:${CHORD_EXTENSION_SOURCE})?|sus(?:2|4)?|(?:add|no|omit)${CHORD_EXTENSION_SOURCE}|${CHORD_EXTENSION_SOURCE})?`;
var CHORD_SYMBOL_SOURCE = String.raw`[A-G](?:#|b)?${CHORD_DECORATION_SOURCE}(?:\/[A-G](?:#|b)?)?`;
var CHORD_SYMBOL_RE = new RegExp(`^${CHORD_SYMBOL_SOURCE}`);
var BARE_CHORD_RE$4 = new RegExp(`^${CHORD_SYMBOL_SOURCE}$`);
var CHORD_ANNOTATION_RE = new RegExp(`^\\[${CHORD_SYMBOL_SOURCE}\\]$`);
var INTRO_DIRECTIVE_RE = /^\{p:\s*#[1-9]\d*\s*\}/;
var INSTRUMENTAL_DIRECTIVE_RE = /^\{c:\s*[A-Za-z0-9 +\-\/#]+\s*\}/;
var INTRO_OR_CUE_DIRECTIVE_RE = /^(?:\{p:\s*#[1-9]\d*\s*\}|\{c:\s*[A-Za-z0-9 +\-\/#]+\s*\})/;
var REPEAT_SUFFIX_RE$1 = /^\([1-9]\d*x\)/;
var DEFAULT_DRAFT_EXAMPLE = getDefaultDraftExample();
function hasChordProgressionText(value, allowZeroWidthSpace = true) {
	const source = String(value ?? "");
	if (!source.includes("|")) return false;
	return source.replace(/(\{[^{}\r\n]+\}|\|\|:|\|:|:\|\||:\||\||\([1-9]\d*x\))/g, " ").split(allowZeroWidthSpace ? /[\s\u200B]+/u : /\s+/).some((segment) => BARE_CHORD_RE$4.test(segment));
}
var DEFAULT_CONTENT = DEFAULT_DRAFT_EXAMPLE.content;
var DEFAULT_PANEL_VISIBILITY = getDefaultPanelVisibilityForCurrentPage();
var state = {
	editor: null,
	editorMode: "monaco",
	currentDocumentContent: DEFAULT_CONTENT,
	lastSavedContent: DEFAULT_CONTENT,
	fileName: DEFAULT_DRAFT_EXAMPLE.fileName,
	sharedDocumentDate: "",
	openLyricPluginAvailable: true,
	openLyricHideKeys: false,
	openLyricHideLeadingBars: false,
	openLyricSimplifyChords: false,
	openLyricShowComments: true,
	openLyricShowNotes: true,
	openLyricStructureKeys: {},
	theme: DEFAULT_THEME,
	highlightInvisibleCharacters: true,
	panelSizeWeights: {
		editor: 1,
		preview: 1,
		openLyric: 1
	},
	editorVisible: DEFAULT_PANEL_VISIBILITY.editorVisible,
	openLyricVisible: DEFAULT_PANEL_VISIBILITY.openLyricVisible,
	previewVisible: DEFAULT_PANEL_VISIBILITY.previewVisible,
	spellcheckLanguageStates: { en: true },
	dirty: false,
	dragDepth: 0,
	errorCount: 0,
	validationTimer: 0
};
var runtime = {
	editorActivityCount: 0,
	unsavedChangesToastTimer: 0,
	keptDraftToastTimer: 0,
	unloadAttemptCount: 0,
	unloadAttemptResetTimer: 0,
	languageRegistered: false,
	monacoBooted: false,
	autoSuggestEnabledContextKey: null,
	invisibleCharacterDecorations: null,
	invisibleCharacterHighlightContextKey: null,
	segmentationSelectionContextKey: null,
	dictionaryMenuDisposables: [],
	dictionaryLookupKey: "",
	lineCommentMenuDisposable: null,
	manualWordCompletionProviderDisposable: null,
	manualWordSuggestionInitialExpiryMs: 0,
	manualWordSuggestionSessionExpiryMs: 0,
	spellcheckActionDisposables: /* @__PURE__ */ new Map(),
	spellcheckMenuDisposables: [],
	spellcheckCustomDictionaryCommandDisposable: null,
	spellcheckContextKeys: /* @__PURE__ */ new Map(),
	spellcheckEnabledContextKey: null
};
function resolveElementRefs(root = document) {
	return {
		app: root.querySelector("[data-ol-ref=\"app\"]"),
		appLoading: document.getElementById("appLoading"),
		appLoadingMessage: document.getElementById("appLoadingMessage"),
		topbar: root.querySelector(".topbar"),
		cancelSharedLinkPasswordBtn: root.querySelector("[data-ol-ref=\"cancelSharedLinkPasswordBtn\"]"),
		closeResetExampleDialogBtn: root.querySelector("[data-ol-ref=\"closeResetExampleDialogBtn\"]"),
		closeShareLinkBtn: root.querySelector("[data-ol-ref=\"closeShareLinkBtn\"]"),
		closeShareLinkQrFullscreenBtn: root.querySelector("[data-ol-ref=\"closeShareLinkQrFullscreenBtn\"]"),
		closeSpellcheckCustomDictionaryBtn: root.querySelector("[data-ol-ref=\"closeSpellcheckCustomDictionaryBtn\"]"),
		addSpellcheckCustomDictionaryWordBtn: root.querySelector("[data-ol-ref=\"addSpellcheckCustomDictionaryWordBtn\"]"),
		addSpellcheckCustomDictionaryExtraWordBtn: root.querySelector("[data-ol-ref=\"addSpellcheckCustomDictionaryExtraWordBtn\"]"),
		copyShareLinkBtn: root.querySelector("[data-ol-ref=\"copyShareLinkBtn\"]"),
		copySpellcheckCustomDictionaryBtn: root.querySelector("[data-ol-ref=\"copySpellcheckCustomDictionaryBtn\"]"),
		copySpellcheckCustomDictionaryEmailBtn: root.querySelector("[data-ol-ref=\"copySpellcheckCustomDictionaryEmailBtn\"]"),
		reportSpellcheckCustomDictionaryBtn: root.querySelector("[data-ol-ref=\"reportSpellcheckCustomDictionaryBtn\"]"),
		editorActions: root.querySelector("[data-ol-ref=\"editorActions\"]"),
		editorActionsBtn: root.querySelector("[data-ol-ref=\"editorActionsBtn\"]"),
		editorActionsContextMenu: root.querySelector("[data-ol-ref=\"editorActionsContextMenu\"]"),
		editorActionsDivider: root.querySelector("[data-ol-ref=\"editorActionsDivider\"]"),
		editorActionsMenu: root.querySelector("[data-ol-ref=\"editorActionsMenu\"]"),
		editorModeToggleMenuSlot: root.querySelector("[data-ol-ref=\"editorModeToggleMenuSlot\"]"),
		editorModeToggleToolbarSlot: root.querySelector("[data-ol-ref=\"editorModeToggleToolbarSlot\"]"),
		editorTranscriptLocaleSelect: root.querySelector("[data-ol-ref=\"editorTranscriptLocaleSelect\"]"),
		editorTranscriptUploadBtn: root.querySelector("[data-ol-ref=\"editorTranscriptUploadBtn\"]"),
		editorTranscriptUploadDialog: root.querySelector("[data-ol-ref=\"editorTranscriptUploadDialog\"]"),
		editorTranscriptUploadForm: root.querySelector("[data-ol-ref=\"editorTranscriptUploadForm\"]"),
		editorTranscriptUploadFileInput: root.querySelector("[data-ol-ref=\"editorTranscriptUploadFileInput\"]"),
		editorTranscriptUploadApiKeyInput: root.querySelector("[data-ol-ref=\"editorTranscriptUploadApiKeyInput\"]"),
		editorTranscriptUploadLocaleSelect: root.querySelector("[data-ol-ref=\"editorTranscriptUploadLocaleSelect\"]"),
		editorTranscriptUploadMessage: root.querySelector("[data-ol-ref=\"editorTranscriptUploadMessage\"]"),
		editorTranscriptUploadPermissionTip: root.querySelector("[data-ol-ref=\"editorTranscriptUploadPermissionTip\"]"),
		editorTranscriptUploadPermissionInstructionBtn: root.querySelector("[data-ol-ref=\"editorTranscriptUploadPermissionInstructionBtn\"]"),
		editorTranscriptUploadPermissionDialog: root.querySelector("[data-ol-ref=\"editorTranscriptUploadPermissionDialog\"]"),
		closeEditorTranscriptUploadPermissionDialogBtn: root.querySelector("[data-ol-ref=\"closeEditorTranscriptUploadPermissionDialogBtn\"]"),
		closeEditorTranscriptUploadBtn: root.querySelector("[data-ol-ref=\"closeEditorTranscriptUploadBtn\"]"),
		submitEditorTranscriptUploadBtn: root.querySelector("[data-ol-ref=\"submitEditorTranscriptUploadBtn\"]"),
		editorTranscriptBrowserWarning: root.querySelector("[data-ol-ref=\"editorTranscriptBrowserWarning\"]"),
		editorTranscriptDownloadChromeWarning: root.querySelector("[data-ol-ref=\"editorTranscriptDownloadChromeWarning\"]"),
		editorTranscriptStatus: root.querySelector("[data-ol-ref=\"editorTranscriptStatus\"]"),
		editorTranscriptToggleBtn: root.querySelector("[data-ol-ref=\"editorTranscriptToggleBtn\"]"),
		editorClearTextBtn: root.querySelector("[data-ol-ref=\"editorClearTextBtn\"]"),
		editorCopyTextBtn: root.querySelector("[data-ol-ref=\"editorCopyTextBtn\"]"),
		editorRedoBtn: root.querySelector("[data-ol-ref=\"editorRedoBtn\"]"),
		editorResetBtn: root.querySelector("[data-ol-ref=\"editorResetBtn\"]"),
		editorSaveBtn: root.querySelector("[data-ol-ref=\"editorSaveBtn\"]"),
		editorHost: root.querySelector("[data-ol-ref=\"editor\"]"),
		editorUndoBtn: root.querySelector("[data-ol-ref=\"editorUndoBtn\"]"),
		simpleEditorTextarea: root.querySelector("[data-ol-ref=\"simpleEditorTextarea\"]"),
		simpleEditorToggleControl: root.querySelector("[data-ol-ref=\"simpleEditorToggleControl\"]"),
		simpleEditorToggle: root.querySelector("[data-ol-ref=\"simpleEditorToggle\"]"),
		fileInput: root.querySelector("[data-ol-ref=\"fileInput\"]"),
		keyboardToggleBtn: root.querySelector("[data-ol-ref=\"keyboardToggleBtn\"]"),
		loadBlankExampleBtn: root.querySelector("[data-ol-ref=\"loadBlankExampleBtn\"]"),
		loadSelectedExampleBtn: root.querySelector("[data-ol-ref=\"loadSelectedExampleBtn\"]"),
		openBtn: root.querySelector("[data-ol-ref=\"openBtn\"]"),
		parseRawTextBtn: root.querySelector("[data-ol-ref=\"parseRawTextBtn\"]"),
		parseRawTextSubmitBtn: root.querySelector("[data-ol-ref=\"parseRawTextSubmitBtn\"]"),
		resetExampleDialog: root.querySelector("[data-ol-ref=\"resetExampleDialog\"]"),
		resetExampleList: root.querySelector("[data-ol-ref=\"resetExampleList\"]"),
		rawTextImportDialog: root.querySelector("[data-ol-ref=\"rawTextImportDialog\"]"),
		rawTextImportForm: root.querySelector("[data-ol-ref=\"rawTextImportForm\"]"),
		rawTextImportMessage: root.querySelector("[data-ol-ref=\"rawTextImportMessage\"]"),
		rawTextImportTextarea: root.querySelector("[data-ol-ref=\"rawTextImportTextarea\"]"),
		clearSpellcheckCustomDictionaryBtn: root.querySelector("[data-ol-ref=\"clearSpellcheckCustomDictionaryBtn\"]"),
		closeRawTextImportBtn: root.querySelector("[data-ol-ref=\"closeRawTextImportBtn\"]"),
		saveBtn: root.querySelector("[data-ol-ref=\"saveBtn\"]"),
		shareLinkBtn: root.querySelector("[data-ol-ref=\"shareLinkBtn\"]"),
		shareLinkDialog: root.querySelector("[data-ol-ref=\"shareLinkDialog\"]"),
		shareLinkEncryptionFields: root.querySelector("[data-ol-ref=\"shareLinkEncryptionFields\"]"),
		shareLinkEncryptionToggle: root.querySelector("[data-ol-ref=\"shareLinkEncryptionToggle\"]"),
		shareLinkMessage: root.querySelector("[data-ol-ref=\"shareLinkMessage\"]"),
		shareLinkModeLinkInput: root.querySelector("[data-ol-ref=\"shareLinkModeLinkInput\"]"),
		shareLinkModeQrLinkInput: root.querySelector("[data-ol-ref=\"shareLinkModeQrLinkInput\"]"),
		shareLinkModeQrTextInput: root.querySelector("[data-ol-ref=\"shareLinkModeQrTextInput\"]"),
		shareLinkPasswordConfirmInput: root.querySelector("[data-ol-ref=\"shareLinkPasswordConfirmInput\"]"),
		shareLinkPasswordInput: root.querySelector("[data-ol-ref=\"shareLinkPasswordInput\"]"),
		shareLinkQrTextChunkFields: root.querySelector("[data-ol-ref=\"shareLinkQrTextChunkFields\"]"),
		shareLinkQrTextChunkLengthInput: root.querySelector("[data-ol-ref=\"shareLinkQrTextChunkLengthInput\"]"),
		shareLinkQrFullscreenDialog: root.querySelector("[data-ol-ref=\"shareLinkQrFullscreenDialog\"]"),
		shareLinkQrFullscreenItems: root.querySelector("[data-ol-ref=\"shareLinkQrFullscreenItems\"]"),
		shareLinkQrFullscreenMessage: root.querySelector("[data-ol-ref=\"shareLinkQrFullscreenMessage\"]"),
		shareLinkQrFullscreenPlaceholder: root.querySelector("[data-ol-ref=\"shareLinkQrFullscreenPlaceholder\"]"),
		shareLinkQrItems: root.querySelector("[data-ol-ref=\"shareLinkQrItems\"]"),
		shareLinkQrMessage: root.querySelector("[data-ol-ref=\"shareLinkQrMessage\"]"),
		shareLinkQrPanel: root.querySelector("[data-ol-ref=\"shareLinkQrPanel\"]"),
		shareLinkQrPlaceholder: root.querySelector("[data-ol-ref=\"shareLinkQrPlaceholder\"]"),
		shareLinkTextarea: root.querySelector("[data-ol-ref=\"shareLinkTextarea\"]"),
		sharedLinkPasswordDialog: root.querySelector("[data-ol-ref=\"sharedLinkPasswordDialog\"]"),
		sharedLinkPasswordForm: root.querySelector("[data-ol-ref=\"sharedLinkPasswordForm\"]"),
		sharedLinkPasswordInput: root.querySelector("[data-ol-ref=\"sharedLinkPasswordInput\"]"),
		sharedLinkPasswordMessage: root.querySelector("[data-ol-ref=\"sharedLinkPasswordMessage\"]"),
		submitSharedLinkPasswordBtn: root.querySelector("[data-ol-ref=\"submitSharedLinkPasswordBtn\"]"),
		downloadBtn: root.querySelector("[data-ol-ref=\"downloadBtn\"]"),
		copyOpenLyricTextBtn: root.querySelector("[data-ol-ref=\"copyOpenLyricTextBtn\"]"),
		downloadOpenLyricImageBtn: root.querySelector("[data-ol-ref=\"downloadOpenLyricImageBtn\"]"),
		downloadOpenLyricPowerPointBtn: root.querySelector("[data-ol-ref=\"downloadOpenLyricPowerPointBtn\"]"),
		editorVersionBadge: root.querySelector("[data-ol-ref=\"editorVersionBadge\"]"),
		openLyricOptions: root.querySelector("[data-ol-ref=\"openLyricOptions\"]"),
		openLyricOptionsBtn: root.querySelector("[data-ol-ref=\"openLyricOptionsBtn\"]"),
		openLyricOptionsMenu: root.querySelector("[data-ol-ref=\"openLyricOptionsMenu\"]"),
		openLyricExportProgress: root.querySelector("[data-ol-ref=\"openLyricExportProgress\"]"),
		openLyricExportProgressBar: root.querySelector("[data-ol-ref=\"openLyricExportProgressBar\"]"),
		openLyricExportProgressLabel: root.querySelector("[data-ol-ref=\"openLyricExportProgressLabel\"]"),
		markdownPreviewOptions: root.querySelector("[data-ol-ref=\"markdownPreviewOptions\"]"),
		markdownPreviewHistory: root.querySelector("[data-ol-ref=\"markdownPreviewHistory\"]"),
		markdownPreviewUndoBtn: root.querySelector("[data-ol-ref=\"markdownPreviewUndoBtn\"]"),
		markdownPreviewRedoBtn: root.querySelector("[data-ol-ref=\"markdownPreviewRedoBtn\"]"),
		markdownPreviewOptionsBtn: root.querySelector("[data-ol-ref=\"markdownPreviewOptionsBtn\"]"),
		markdownPreviewOptionsMenu: root.querySelector("[data-ol-ref=\"markdownPreviewOptionsMenu\"]"),
		markdownPreviewExportProgress: root.querySelector("[data-ol-ref=\"markdownPreviewExportProgress\"]"),
		markdownPreviewExportProgressBar: root.querySelector("[data-ol-ref=\"markdownPreviewExportProgressBar\"]"),
		markdownPreviewExportProgressLabel: root.querySelector("[data-ol-ref=\"markdownPreviewExportProgressLabel\"]"),
		markdownPreviewDocxFileNameInput: root.querySelector("[data-ol-ref=\"markdownPreviewDocxFileNameInput\"]"),
		downloadMarkdownPreviewImageBtn: root.querySelector("[data-ol-ref=\"downloadMarkdownPreviewImageBtn\"]"),
		downloadMarkdownPreviewDocxBtn: root.querySelector("[data-ol-ref=\"downloadMarkdownPreviewDocxBtn\"]"),
		goToMarkdownDocBtn: root.querySelector("[data-ol-ref=\"goToMarkdownDocBtn\"]"),
		printOpenLyricBtn: root.querySelector("[data-ol-ref=\"printOpenLyricBtn\"]"),
		printMarkdownPreviewBtn: root.querySelector("[data-ol-ref=\"printMarkdownPreviewBtn\"]"),
		previewOpenLyricHideBarsBtn: root.querySelector("[data-ol-ref=\"previewOpenLyricHideBarsBtn\"]"),
		previewOpenLyricHideKeysBtn: root.querySelector("[data-ol-ref=\"previewOpenLyricHideKeysBtn\"]"),
		previewOpenLyricShowCommentsToggle: root.querySelector("[data-ol-ref=\"previewOpenLyricShowCommentsToggle\"]"),
		previewOpenLyricShowNotesToggle: root.querySelector("[data-ol-ref=\"previewOpenLyricShowNotesToggle\"]"),
		previewOpenLyricSimplifyBtn: root.querySelector("[data-ol-ref=\"previewOpenLyricSimplifyBtn\"]"),
		previewSettings: root.querySelector("[data-ol-ref=\"previewSettings\"]"),
		previewSettingsBtn: root.querySelector("[data-ol-ref=\"previewSettingsBtn\"]"),
		previewSettingsMenu: root.querySelector("[data-ol-ref=\"previewSettingsMenu\"]"),
		previewStructureKeyNextBtn: root.querySelector("[data-ol-ref=\"previewStructureKeyNextBtn\"]"),
		previewStructureKeyPreviousBtn: root.querySelector("[data-ol-ref=\"previewStructureKeyPreviousBtn\"]"),
		previewStructureKeySelect: root.querySelector("[data-ol-ref=\"previewStructureKeySelect\"]"),
		formatDocumentBtn: root.querySelector("[data-ol-ref=\"formatDocumentBtn\"]"),
		resetBtn: root.querySelector("[data-ol-ref=\"resetBtn\"]"),
		resetPreviewTypographyBtn: root.querySelector("[data-ol-ref=\"resetPreviewTypographyBtn\"]"),
		toggleChordBarsBtn: root.querySelector("[data-ol-ref=\"toggleChordBarsBtn\"]"),
		toggleEditorBtn: root.querySelector("[data-ol-ref=\"toggleEditorBtn\"]"),
		shellResizeHandles: root.querySelector("[data-ol-ref=\"shellResizeHandles\"]"),
		spellcheckToggleBtn: root.querySelector("[data-ol-ref=\"spellcheckToggleBtn\"]"),
		toggleOpenLyricBtn: root.querySelector("[data-ol-ref=\"toggleOpenLyricBtn\"]"),
		togglePreviewBtn: root.querySelector("[data-ol-ref=\"togglePreviewBtn\"]"),
		themeToggleBtn: root.querySelector("[data-ol-ref=\"themeToggleBtn\"]"),
		themeMenu: root.querySelector("[data-ol-ref=\"themeMenu\"]"),
		topbarMeta: root.querySelector("[data-ol-ref=\"topbarMeta\"]"),
		topbarActions: root.querySelector("[data-ol-ref=\"topbarActions\"]"),
		topbarActionsBtn: root.querySelector("[data-ol-ref=\"topbarActionsBtn\"]"),
		topbarActionsMenu: root.querySelector("[data-ol-ref=\"topbarActionsMenu\"]"),
		topbarResetBtn: root.querySelector("[data-ol-ref=\"topbarResetBtn\"]"),
		topbarSaveBtn: root.querySelector("[data-ol-ref=\"topbarSaveBtn\"]"),
		editorPanel: root.querySelector("[data-ol-ref=\"editorPanel\"]"),
		openLyricPanel: root.querySelector("[data-ol-ref=\"openLyricPanel\"]"),
		openLyricPreview: root.querySelector("[data-ol-ref=\"openLyricPreview\"]"),
		preview: root.querySelector("[data-ol-ref=\"preview\"]"),
		previewPanel: root.querySelector("[data-ol-ref=\"previewPanel\"]"),
		shell: root.querySelector("[data-ol-ref=\"shell\"]"),
		spellcheckCustomDictionaryDialog: root.querySelector("[data-ol-ref=\"spellcheckCustomDictionaryDialog\"]"),
		spellcheckExcludedWordsList: root.querySelector("[data-ol-ref=\"spellcheckExcludedWordsList\"]"),
		spellcheckCustomDictionaryEmptyState: root.querySelector("[data-ol-ref=\"spellcheckCustomDictionaryEmptyState\"]"),
		spellcheckCustomDictionaryLanguageSelect: root.querySelector("[data-ol-ref=\"spellcheckCustomDictionaryLanguageSelect\"]"),
		spellcheckCustomDictionaryExtraLanguageSelect: root.querySelector("[data-ol-ref=\"spellcheckCustomDictionaryExtraLanguageSelect\"]"),
		spellcheckCustomDictionaryList: root.querySelector("[data-ol-ref=\"spellcheckCustomDictionaryList\"]"),
		spellcheckCustomDictionaryMessage: root.querySelector("[data-ol-ref=\"spellcheckCustomDictionaryMessage\"]"),
		spellcheckCustomDictionaryWordInput: root.querySelector("[data-ol-ref=\"spellcheckCustomDictionaryWordInput\"]"),
		spellcheckCustomDictionaryExtraWordInput: root.querySelector("[data-ol-ref=\"spellcheckCustomDictionaryExtraWordInput\"]"),
		sharedDocumentDate: root.querySelector("[data-ol-ref=\"sharedDocumentDate\"]"),
		status: root.querySelector("[data-ol-ref=\"status\"]"),
		unsavedChangesToast: root.querySelector("[data-ol-ref=\"unsavedChangesToast\"]"),
		unsavedChangesToastAttempts: root.querySelector("[data-ol-ref=\"unsavedChangesToastAttempts\"]"),
		keptDraftToast: root.querySelector("[data-ol-ref=\"keptDraftToast\"]"),
		keptDraftToastText: root.querySelector("[data-ol-ref=\"keptDraftToastText\"]"),
		keptDraftToastOpenBtn: root.querySelector("[data-ol-ref=\"keptDraftToastOpenBtn\"]")
	};
}
var refs = resolveElementRefs();
function syncEditorVersionBadge() {
	if (!refs.editorVersionBadge) return;
	const metadataLabel = getEditorMetadataTitle();
	refs.editorVersionBadge.textContent = getEditorVersionBadgeText();
	refs.editorVersionBadge.title = metadataLabel;
	refs.editorVersionBadge.setAttribute("aria-label", metadataLabel);
}
syncEditorVersionBadge();
syncEditorActivityState();
syncEditorDirtyState();
function syncEditorActivityState() {
	if (!(refs.editorPanel instanceof HTMLElement)) return;
	refs.editorPanel.dataset.activityState = runtime.editorActivityCount > 0 ? "busy" : "idle";
}
/**
* Mirror the unsaved-changes flag onto the editor panel as `data-dirty`, which
* is what paints the panel's red top border (`styles/shell.scss`), and onto
* the editor tools menu's document group, whose Reset and Save buttons are
* enabled only while there is something to discard or write.
*
* It tracks `state.dirty` exactly, so both markers mean the same condition the
* unload guard prompts on — see
* `OpenLyricEditorApplication.handleWindowBeforeUnload`. "Dirty" here means
* *not written to disk*: every keystroke still autosaves the draft to browser
* storage, so a reload restores the text either way.
*/
function syncEditorDirtyState() {
	if (refs.editorPanel instanceof HTMLElement) refs.editorPanel.dataset.dirty = state.dirty ? "true" : "false";
	for (const button of [
		refs.editorResetBtn,
		refs.editorSaveBtn,
		refs.topbarResetBtn,
		refs.topbarSaveBtn
	]) if (button instanceof HTMLButtonElement) button.disabled = !state.dirty;
}
/**
* Split document text into lines the way a line number addresses it: line 1 is
* `lines[0]`, and a trailing newline is a line terminator rather than an extra
* empty line at the end.
*/
function splitDocumentLines(text) {
	return String(text ?? "").replace(/\r\n?/g, "\n").split("\n");
}
/**
* The pure text half of {@link replaceDocumentLineRange} — kept separate so the
* write-back rule ("given this source and this input, the document becomes
* exactly that") can be asserted without an editor surface in play.
*
* `endLineNumber === startLineNumber - 1` is the insertion form: nothing is
* consumed and `nextLines` land before `startLineNumber`. That is what an
* empty fence body needs, since it has no lines of its own to replace.
*/
function replaceTextLineRange(text, startLineNumber, endLineNumber, nextLines) {
	const lines = splitDocumentLines(text);
	const start = Math.max(Math.trunc(Number(startLineNumber) || 0), 1);
	const end = Math.trunc(Number(endLineNumber) || 0);
	if (start > lines.length + 1 || end < start - 1 || end > lines.length) return null;
	const insertedLines = Array.isArray(nextLines) ? nextLines.map((line) => String(line ?? "")) : [];
	return [
		...lines.slice(0, start - 1),
		...insertedLines,
		...lines.slice(end)
	].join("\n");
}
var grammar = {
	FORM_SECTION_NAMES,
	LYRIC_SECTION_NAMES,
	INSTRUMENTAL_SECTION_NAMES,
	FREE_TEXT_SECTION_NAMES,
	NUMBERED_SECTION_NAMES,
	CONFIG_FIELD_ALIASES,
	CONFIG_FIELD_NAMES: CONFIG_FIELD_NAMES$1,
	CONFIG_FIELD_MATCH_NAMES: CONFIG_FIELD_MATCH_NAMES$1,
	CONFIG_REQUIRED_FIELD_NAMES: CONFIG_REQUIRED_FIELD_NAMES$1,
	CONFIG_MULTILINE_FIELD_NAMES: CONFIG_MULTILINE_FIELD_NAMES$1,
	CONFIG_KEY_VALUES,
	CONFIG_LOCALE_SEPARATOR: ",",
	CONFIG_LOCALE_VALUES,
	CONFIG_ENUM_FIELD_VALUES: CONFIG_ENUM_FIELD_VALUES$1,
	CONFIG_PATTERN_FIELD_VALUES: CONFIG_PATTERN_FIELD_VALUES$1,
	CONFIG_PATTERN_FIELD_MESSAGES: CONFIG_PATTERN_FIELD_MESSAGES$1,
	CHORD_KEY_GROUPS,
	CONFIG_HEADER_RE,
	INTRO_HEADER_RE,
	INSTRUMENTAL_HEADER_RE,
	LYRIC_HEADER_RE,
	FREE_TEXT_HEADER_RE
};
//#endregion
//#region src/plugins/OpenLyric/domain/parser/fences/OLFenceDefinition.ts
var PREVIEW_COMMENT_LINE_RE = /^\s*\/\//;
function formatDeclaredPartName(header, indexText = "") {
	return indexText ? `${header} ${indexText}` : header;
}
function createHeaderInfoPattern(header, allowsNumbering) {
	return new RegExp(`^${escapeRegex(header)}${allowsNumbering ? String.raw`(?:\s+([1-9]\d*))?` : ""}$`);
}
function createFenceHeaderPattern(header, allowsNumbering) {
	return new RegExp("^\\s*```ol:" + escapeRegex(header) + (allowsNumbering ? String.raw`(?:\s+[1-9]\d*)?` : "") + "\\s*$");
}
function createTokenizerFenceHeaderPattern(header, allowsNumbering) {
	return new RegExp("^(\\s*```ol:)(" + escapeRegex(header) + (allowsNumbering ? String.raw`(?:\s+[1-9]\d*)?` : "") + ")(\\s*)$");
}
function normalizeTokenClass(value) {
	return String(value || "").trim().toLowerCase().replace(/[^a-z0-9]+/g, "-").replace(/^-+|-+$/g, "");
}
function createVariantDocumentation(description) {
	return description.endsWith(".") ? `${description.slice(0, -1)} variant.` : `${description} variant.`;
}
/**
* How many source lines sit between the fence's opening and closing lines.
*
* Deliberately *not* {@link OLFenceDefinition.getPreviewLines}: that drops
* comment lines, and a line range written back into the document has to count
* every line the source actually has. A non-empty body always ends in the
* newline before the closing fence, so that terminator is not a line of its
* own — but a body of a single blank line is one line, which is why the
* empty-string check comes first.
*/
function countFenceBodySourceLines(body) {
	const normalizedBody = String(body ?? "").replace(/\r\n?/g, "\n");
	if (!normalizedBody.length) return 0;
	return normalizedBody.endsWith("\n") ? normalizedBody.slice(0, -1).split("\n").length : normalizedBody.split("\n").length;
}
/**
* The rename glyph beside a section card's title
* (`ol-preview-fence__rename`) — a luggage-tag outline.
*
* Deliberately *not* {@link PREVIEW_EDIT_ICON_SVG}: the same header already
* carries a pencil for "edit this section's lyrics", and two identical pencils
* a few centimetres apart is exactly the ambiguity a reader who never opens the
* text panel cannot resolve.
*/
var PREVIEW_RENAME_ICON_SVG = "<svg viewBox=\"0 0 16 16\" fill=\"currentColor\" aria-hidden=\"true\" focusable=\"false\"><path d=\"M2 2a1 1 0 0 0-1 1v4.586a1 1 0 0 0 .293.707l7 7a1 1 0 0 0 1.414 0l4.586-4.586a1 1 0 0 0 0-1.414l-7-7A1 1 0 0 0 6.586 2zm0 1h4.586l7 7-4.586 4.586-7-7zm2.5 1a1.5 1.5 0 1 0 0 3 1.5 1.5 0 0 0 0-3m0 1a.5.5 0 1 1 0 1 .5.5 0 0 1 0-1\"/></svg>";
/**
* The bin glyph in a section card header (`ol-preview-fence__delete`).
*
* Icon-only like its neighbours, and last in the header: a destructive control
* a reader can reach by mistake is worse than one they have to aim at.
*/
var PREVIEW_DELETE_ICON_SVG = "<svg viewBox=\"0 0 16 16\" fill=\"currentColor\" aria-hidden=\"true\" focusable=\"false\"><path d=\"M6.5 1a.5.5 0 0 0-.5.5V2H2.5a.5.5 0 0 0 0 1H3v10.5A1.5 1.5 0 0 0 4.5 15h7a1.5 1.5 0 0 0 1.5-1.5V3h.5a.5.5 0 0 0 0-1H10v-.5a.5.5 0 0 0-.5-.5zM7 2h2v-.5H7zM4 3h8v10.5a.5.5 0 0 1-.5.5h-7a.5.5 0 0 1-.5-.5zm2 2a.5.5 0 0 1 .5.5v6a.5.5 0 0 1-1 0v-6A.5.5 0 0 1 6 5m4 0a.5.5 0 0 1 .5.5v6a.5.5 0 0 1-1 0v-6A.5.5 0 0 1 10 5\"/></svg>";
/** The pencil in a section card header (`ol-preview-fence__edit`). */
var PREVIEW_EDIT_ICON_SVG = "<svg viewBox=\"0 0 16 16\" fill=\"currentColor\" aria-hidden=\"true\" focusable=\"false\"><path d=\"M12.146.146a.5.5 0 0 1 .708 0l3 3a.5.5 0 0 1 0 .708l-10 10a.5.5 0 0 1-.168.11l-5 2a.5.5 0 0 1-.65-.65l2-5a.5.5 0 0 1 .11-.168zM11.207 2.5 13.5 4.793 14.793 3.5 12.5 1.207zm1.586 3L10.5 3.207 4 9.707V10h.5a.5.5 0 0 1 .5.5v.5h.5a.5.5 0 0 1 .5.5v.5h.293zm-9.761 5.175-.106.106-1.528 3.821 3.821-1.528.106-.106A.5.5 0 0 1 5 12.5V12h-.5a.5.5 0 0 1-.5-.5V11h-.5a.5.5 0 0 1-.468-.325\"/></svg>";
function normalizePreviewBodyLines(body) {
	const normalizedBody = String(body ?? "").replace(/\r\n?/g, "\n");
	const trimmedBody = normalizedBody.endsWith("\n") ? normalizedBody.slice(0, -1) : normalizedBody;
	if (!trimmedBody.length) return [];
	return trimmedBody.split("\n").filter((line) => !PREVIEW_COMMENT_LINE_RE.test(line));
}
var OLFenceDefinition = class {
	constructor({ className, header, kind, description, tokenState, allowsNumbering = false, required = false, links = [], allowDuplicateDeclarations = false }) {
		this.className = className;
		this.header = header;
		this.kind = kind;
		this.description = description;
		this.tokenState = tokenState;
		this.allowsNumbering = allowsNumbering;
		this.required = required;
		this.links = links.slice();
		this.allowDuplicateDeclarations = allowDuplicateDeclarations;
		this.tokenClass = normalizeTokenClass(header);
		this.headerInfoPattern = createHeaderInfoPattern(header, allowsNumbering);
		this.fenceHeaderPattern = createFenceHeaderPattern(header, allowsNumbering);
		this.tokenizerFenceHeaderPattern = createTokenizerFenceHeaderPattern(header, allowsNumbering);
	}
	createHeaderInfo(indexText = "") {
		return {
			definition: this,
			className: this.className,
			header: this.header,
			label: this.header,
			kind: this.kind,
			indexText,
			partName: formatDeclaredPartName(this.header, indexText)
		};
	}
	parseHeader(info) {
		const match = info.match(this.headerInfoPattern);
		if (!match) return null;
		return this.createHeaderInfo(match[1] || "");
	}
	getTokenizerRootRule() {
		return [this.tokenizerFenceHeaderPattern, [
			"ol-fence",
			{
				token: `ol-fence-title.${this.tokenClass}`,
				next: `@${this.tokenState}`
			},
			"ol-fence"
		]];
	}
	getTokenizerStateRules(context) {
		return context.stateRules[this.tokenState] || context.stateRules.olUnknown;
	}
	getSnippetHeaders() {
		return this.allowsNumbering ? [this.header, `${this.header} 1`] : [this.header];
	}
	getSnippetDefinitions() {
		return this.getSnippetHeaders().map((header, index) => ({
			definition: this,
			header,
			documentation: index === 0 ? this.description : createVariantDocumentation(this.description)
		}));
	}
	getSnippetBodyLines() {
		return ["$0"];
	}
	allowsDuplicateDeclaredPart() {
		return this.allowDuplicateDeclarations;
	}
	getLinkedFenceHeaders() {
		return this.links.slice();
	}
	getLinkedFences(registry) {
		return this.getLinkedFenceHeaders().map((header) => registry.findByHeader(header)).filter(Boolean);
	}
	getPreviewTitle(parsedHeader) {
		return parsedHeader?.partName || (parsedHeader?.header ? `ol:${parsedHeader.header}` : `ol:${this.header}`);
	}
	getPreviewLines(body) {
		return normalizePreviewBodyLines(body);
	}
	renderPreviewBody(context) {
		return context.helpers.renderLineCollection(context.lineEntries);
	}
	renderPreview(context) {
		const parsedHeader = context.parsedHeader || this.createHeaderInfo();
		const header = parsedHeader.header || this.header || "unknown";
		const kind = parsedHeader.kind || this.kind || "unknown";
		const title = this.getPreviewTitle(parsedHeader, context);
		const sourceLocation = context.sourceLocation || null;
		const lineEntries = context.lineEntries || context.helpers.createPreviewLineEntries(context.body, sourceLocation);
		const lines = context.lines || lineEntries.map((entry) => entry.text);
		const targetId = context.helpers.createPreviewTargetId(parsedHeader.partName || title);
		const editorLine = sourceLocation?.bodyLineNumber || "";
		const editorColumn = sourceLocation?.bodyColumn || "";
		const previewContext = {
			...context,
			header,
			parsedHeader,
			kind,
			title,
			lines,
			lineEntries,
			sourceLocation,
			targetId
		};
		return [
			`<details class="ol-preview-fence ol-preview-fence--${context.helpers.escapeHtml(kind)}" data-ol-kind="${context.helpers.escapeHtml(kind)}" data-ol-header="${context.helpers.escapeHtml(header)}"${targetId ? ` id="${context.helpers.escapeHtml(targetId)}"` : ""}${context.helpers.getEditorDataAttributes(editorLine, editorColumn)} open>`,
			"<summary class=\"ol-preview-fence__summary\">",
			`<span class="ol-preview-fence__title"${context.helpers.getFenceHeaderEditorDataAttributes(sourceLocation?.startLineNumber || "")}>${context.helpers.escapeHtml(title)}</span>`,
			this.renderPreviewRenameAction(previewContext),
			this.renderPreviewEditAction(previewContext),
			this.renderPreviewDeleteAction(previewContext),
			"</summary>",
			`<div class="ol-preview-fence__body">${this.renderPreviewBody(previewContext)}</div>`,
			"</details>",
			this.renderPreviewAfterCard(previewContext)
		].join("");
	}
	/**
	* Whether this section's body can be edited as raw notation from the
	* preview. `Config` says no: it renders one purpose-built control per field
	* already, and a second, free-text way to rewrite the same lines would put
	* two editors on one source range.
	*/
	isPreviewBodyEditable() {
		return true;
	}
	/**
	* How the section editor's chord picker writes a chord into this body.
	*
	* - `annotation` — `[G]` before the syllable (lyric and free-text bodies).
	* - `progression` — a bare, space-separated `G` (a body that is one chord
	*   progression, where a bracket would be an invalid token).
	* - `mixed` — decided per line: bare on a line that already reads as a
	*   progression (a `|` beside a chord, or a `{c:}`/`{p:}` cue), `[G]`
	*   everywhere else.
	*/
	getPreviewChordInsertStyle() {
		return "annotation";
	}
	/**
	* The pencil at the right end of the section card header — the entry point
	* for editing this section's lyrics without opening the text panel.
	*
	* It carries the body's own source line range rather than a DOM hook, so the
	* controller seeds its editor from the document and writes back to the same
	* lines. `data-preview-body-end-line` is one *below* the start line when the
	* body is empty, which the write-back reads as "insert here".
	*/
	renderPreviewEditAction(context) {
		if (!this.isPreviewBodyEditable()) return "";
		const startLineNumber = Number(context.sourceLocation?.startLineNumber) || 0;
		if (!startLineNumber) return "";
		const bodyStartLineNumber = startLineNumber + 1;
		const bodyEndLineNumber = startLineNumber + countFenceBodySourceLines(context.body);
		const label = `Edit ${context.title || this.header} text`;
		const escapedLabel = context.helpers.escapeHtml(label);
		return `<button class="ol-preview-fence__edit" type="button" data-preview-action="edit-section-body" data-preview-body-start-line="${bodyStartLineNumber}" data-preview-body-end-line="${bodyEndLineNumber}" data-preview-section-label="${context.helpers.escapeHtml(context.title || this.header)}" data-preview-chord-style="${context.helpers.escapeHtml(this.getPreviewChordInsertStyle())}" aria-label="${escapedLabel}" title="${escapedLabel}">${PREVIEW_EDIT_ICON_SVG}</button>`;
	}
	/**
	* Whether this section's ```` ```ol:… ```` header can be renamed from the
	* preview. Follows {@link isPreviewBodyEditable} by default, so `Config` —
	* which cannot be numbered or suffixed at all — never grows a rename
	* control.
	*/
	isPreviewTitleEditable() {
		return this.isPreviewBodyEditable();
	}
	/**
	* The rename control beside a section card's title — how `Verse 1` becomes
	* `Verse 3` without opening the text panel.
	*
	* Only the header's own source line number travels on it, plus the part name
	* the card was rendered from. The write-back
	* (`preview/controller/section-naming.ts`) re-reads that line and checks it
	* still declares this part before replacing it, so a control left behind by
	* stale markup renames nothing.
	*/
	renderPreviewRenameAction(context) {
		if (!this.isPreviewTitleEditable()) return "";
		const startLineNumber = Number(context.sourceLocation?.startLineNumber) || 0;
		if (!startLineNumber) return "";
		const parsedHeader = context.parsedHeader || this.createHeaderInfo();
		const partName = parsedHeader.partName || this.header;
		const label = `Rename ${partName}`;
		const escapedLabel = context.helpers.escapeHtml(label);
		return `<button class="ol-preview-fence__rename" type="button" data-preview-action="edit-section-title" data-preview-header-line="${startLineNumber}" data-preview-part-name="${context.helpers.escapeHtml(partName)}" data-preview-part-header="${context.helpers.escapeHtml(parsedHeader.header || this.header)}" data-preview-part-index="${context.helpers.escapeHtml(parsedHeader.indexText || "")}" aria-expanded="false" aria-label="${escapedLabel}" title="${escapedLabel}">${PREVIEW_RENAME_ICON_SVG}</button>`;
	}
	/**
	* Whether this section can be deleted from the preview. Follows
	* {@link isPreviewBodyEditable}, so `Config` — which every song must have —
	* never grows a bin.
	*/
	isPreviewSectionDeletable() {
		return this.isPreviewBodyEditable();
	}
	/**
	* The bin at the end of a section card header.
	*
	* It carries the fence's *whole* source range — its opening line through its
	* closing line — because deleting is the one edit that consumes the header
	* too. The body line count is the same count
	* {@link renderPreviewEditAction} uses, plus one for the closing fence.
	*
	* The part name rides along so the write-back can re-read the header line and
	* check it still declares this section before removing anything, the same
	* stale-markup guard the rename uses.
	*/
	renderPreviewDeleteAction(context) {
		if (!this.isPreviewSectionDeletable()) return "";
		const startLineNumber = Number(context.sourceLocation?.startLineNumber) || 0;
		if (!startLineNumber) return "";
		const partName = (context.parsedHeader || this.createHeaderInfo()).partName || this.header;
		const endLineNumber = startLineNumber + countFenceBodySourceLines(context.body) + 1;
		const label = `Delete ${partName}`;
		const escapedLabel = context.helpers.escapeHtml(label);
		return `<button class="ol-preview-fence__delete" type="button" data-preview-action="delete-section" data-preview-fence-start-line="${startLineNumber}" data-preview-fence-end-line="${endLineNumber}" data-preview-part-name="${context.helpers.escapeHtml(partName)}" aria-haspopup="dialog" aria-expanded="false" aria-label="${escapedLabel}" title="${escapedLabel}">${PREVIEW_DELETE_ICON_SVG}</button>`;
	}
	/**
	* Markup this fence contributes *after* its own card, in the gap before the
	* next one. Empty for every section; `Config` uses it for the "Add Lyric"
	* control, which is why the hook exists rather than a central switch in the
	* panel renderer.
	*/
	renderPreviewAfterCard() {
		return "";
	}
	/**
	* Markup the markdown preview shows for a document with nothing in it.
	* Empty for every section; `Config` — the one required part — uses it for
	* the "Start a new song" control (`renderOpenLyricEmptyDocumentHtml`).
	*/
	renderPreviewEmptyDocument(_context) {
		return "";
	}
	validateBody() {}
};
//#endregion
//#region src/plugins/OpenLyric/domain/parser/fences/OLLyricFence.ts
var OLLyricFence = class extends OLFenceDefinition {
	constructor(options) {
		super({
			...options,
			kind: "lyric",
			tokenState: "olLyric"
		});
	}
	validateBody(context) {
		context.validators.validateLyricBlock(context.bodyLines, context.startLineNumber, context.markers);
	}
	renderPreviewBody(context) {
		return context.helpers.renderLyricLineCollection(context.lineEntries);
	}
};
//#endregion
//#region src/plugins/OpenLyric/domain/parser/fences/OLBridge.ts
var OLBridge = class extends OLLyricFence {
	constructor() {
		super({
			className: "OLBridge",
			header: "Bridge",
			description: "Lyric section fence.",
			allowsNumbering: true
		});
	}
};
//#endregion
//#region src/plugins/OpenLyric/domain/parser/fences/OLFreeTextFence.ts
var OLFreeTextFence = class extends OLFenceDefinition {
	constructor(options) {
		super({
			...options,
			kind: "freeText",
			tokenState: "olFreeText"
		});
	}
};
//#endregion
//#region src/plugins/OpenLyric/domain/parser/fences/OLBreakdown.ts
var OLBreakdown = class extends OLFreeTextFence {
	constructor() {
		super({
			className: "OLBreakdown",
			header: "Breakdown",
			description: "Free-text section fence.",
			allowsNumbering: true
		});
	}
};
//#endregion
//#region src/plugins/OpenLyric/domain/parser/fences/OLChorus.ts
var OLChorus = class extends OLLyricFence {
	constructor() {
		super({
			className: "OLChorus",
			header: "Chorus",
			allowsNumbering: true,
			description: "Lyric section fence."
		});
	}
};
//#endregion
//#region src/plugins/OpenLyric/domain/attachments.ts
/** `[label](url)` — the Markdown link form an attachment line may take. */
var MARKDOWN_LINK_RE = /^\[([^\]\r\n]+)\]\((\S[^\r\n)]*)\)$/;
var EXTENSION_TYPES = {
	aac: "audio",
	flac: "audio",
	m4a: "audio",
	mp3: "audio",
	oga: "audio",
	ogg: "audio",
	opus: "audio",
	wav: "audio",
	weba: "audio",
	wma: "audio",
	avi: "video",
	m4v: "video",
	mkv: "video",
	mov: "video",
	mp4: "video",
	mpeg: "video",
	mpg: "video",
	ogv: "video",
	webm: "video",
	wmv: "video",
	pdf: "pdf",
	avif: "image",
	bmp: "image",
	gif: "image",
	heic: "image",
	ico: "image",
	jpeg: "image",
	jpg: "image",
	png: "image",
	svg: "image",
	tif: "image",
	tiff: "image",
	webp: "image"
};
var YOUTUBE_HOSTS = [
	"youtube.com",
	"youtu.be",
	"youtube-nocookie.com",
	"youtubekids.com"
];
/**
* The URL split into the two parts the guesses below need. `URL` parses every
* scheme the field allows — `https:`, `file:`, and app schemes such as
* `vscode://file/C:/song.md` — so a failure here means a string that is not a
* URL at all, and the caller falls back to the raw text.
*/
function parseAttachmentUrl(link) {
	try {
		const url = new URL(link);
		return {
			host: url.hostname.replace(/^www\./, "").toLowerCase(),
			path: url.pathname
		};
	} catch {
		return null;
	}
}
/** The last non-empty segment of a path, percent-decoded where it can be. */
function getLastPathSegment(path) {
	const segment = path.split("/").filter(Boolean).pop() ?? "";
	if (!segment) return "";
	try {
		return decodeURIComponent(segment);
	} catch {
		return segment;
	}
}
function getFileExtension(path) {
	const segment = getLastPathSegment(path);
	const dotIndex = segment.lastIndexOf(".");
	if (dotIndex <= 0 || dotIndex === segment.length - 1) return "";
	return segment.slice(dotIndex + 1).toLowerCase();
}
function isYouTubeHost(host) {
	return YOUTUBE_HOSTS.some((youtubeHost) => host === youtubeHost || host.endsWith(`.${youtubeHost}`));
}
/**
* What the link points at. The query string is deliberately not consulted: a
* `?list=…` or a signed-download token says nothing about the file, and the
* extension of the *path* is the only part of a URL that does.
*/
function getOpenLyricAttachmentType(link) {
	const parsed = parseAttachmentUrl(link);
	if (!parsed) return "other";
	if (isYouTubeHost(parsed.host)) return "youtube";
	return EXTENSION_TYPES[getFileExtension(parsed.path)] ?? "other";
}
function createAttachmentTitle(link) {
	const parsed = parseAttachmentUrl(link);
	if (!parsed) return link;
	return getLastPathSegment(parsed.path) || parsed.host || link;
}
/**
* One attachment line as a record, or `null` when the line is blank. Anything
* that is not a URL still comes back — as `other`, titled with the text itself
* — because a song is edited live and half-typed lines are normal; it is
* `validation.ts` that tells the writer about them, not this reader.
*/
function parseOpenLyricAttachmentLine(line) {
	const text = String(line ?? "").trim();
	if (!text) return null;
	const markdownLink = MARKDOWN_LINK_RE.exec(text);
	const link = (markdownLink ? markdownLink[2] : text).trim();
	return {
		title: (markdownLink ? markdownLink[1].trim() : "") || createAttachmentTitle(link),
		type: getOpenLyricAttachmentType(link),
		link
	};
}
/** Every attachment line of a Config, in the order they are written. */
function createOpenLyricAttachments(lines) {
	return (Array.isArray(lines) ? lines : []).map((line) => parseOpenLyricAttachmentLine(line)).filter((attachment) => Boolean(attachment));
}
//#endregion
//#region src/plugins/OpenLyric/domain/music-theory.ts
var CHORD_DATABASE_ROOTS_BY_CHROMA = [
	"C",
	"Csharp",
	"D",
	"Eb",
	"E",
	"F",
	"Fsharp",
	"G",
	"Ab",
	"A",
	"Bb",
	"B"
];
function normalizeMusicTheoryText(value) {
	return String(value ?? "").trim().replace(/♯/g, "#").replace(/♭/g, "b");
}
function normalizeChordText(value) {
	return normalizeMusicTheoryText(value).replace(/\s+/g, "");
}
function normalizePitchClass(value) {
	return pitchClass(normalizeMusicTheoryText(value)) || "";
}
function getPitchClassChroma(value) {
	const chroma$1 = chroma(value);
	return Number.isFinite(chroma$1) ? chroma$1 : null;
}
function parseMainKey(keyText) {
	const normalizedKeyText = normalizeMusicTheoryText(keyText);
	if (!normalizedKeyText) return null;
	const match = normalizedKeyText.match(/^([A-Ga-g](?:#|b)?)(m)?$/);
	if (!match) return null;
	const tonic = normalizePitchClass(match[1]);
	if (!tonic) return null;
	const isMinor = match[2] === "m";
	const keyData = isMinor ? minorKey(tonic) : majorKey(tonic);
	const chroma = getPitchClassChroma(keyData.tonic);
	if (!keyData.tonic || chroma == null) return null;
	return {
		raw: `${keyData.tonic}${isMinor ? "m" : ""}`,
		tonic: keyData.tonic,
		chroma,
		isMinor,
		alteration: Number.isFinite(keyData.alteration) ? keyData.alteration : 0,
		keySignature: String(keyData.keySignature || "")
	};
}
function normalizeStructureKeyOption(value) {
	const parsedKey = parseMainKey(value);
	return parsedKey ? parsedKey.raw : normalizeMusicTheoryText(value);
}
function createPitchClassCandidates(chroma) {
	const normalizedChroma = (Number(chroma) % 12 + 12) % 12;
	const intervalName = fromSemitones(normalizedChroma);
	const flatCandidate = normalizePitchClass(simplify(transpose("C", intervalName)));
	return {
		flatCandidate,
		sharpCandidate: normalizePitchClass(enharmonic(flatCandidate) || flatCandidate) || flatCandidate
	};
}
function choosePreferredPitchClass(chroma, targetKey) {
	const { flatCandidate, sharpCandidate } = createPitchClassCandidates(chroma);
	if (!flatCandidate) return "";
	if (!sharpCandidate || sharpCandidate === flatCandidate) return flatCandidate;
	if (!targetKey) return flatCandidate;
	if (targetKey.alteration > 0 || targetKey.raw.includes("#")) return sharpCandidate;
	if (targetKey.alteration < 0 || targetKey.raw.includes("b")) return flatCandidate;
	if (!/[#b]/.test(flatCandidate)) return flatCandidate;
	if (!/[#b]/.test(sharpCandidate)) return sharpCandidate;
	return flatCandidate;
}
function transposePitchClass(noteText, semitoneOffset, targetKeyText) {
	const pitchClass = normalizePitchClass(noteText);
	const pitchClassChroma = getPitchClassChroma(pitchClass);
	if (!pitchClass || pitchClassChroma == null) return normalizeMusicTheoryText(noteText);
	return choosePreferredPitchClass(pitchClassChroma + Number(semitoneOffset), parseMainKey(targetKeyText)) || pitchClass;
}
function transposeChordSymbol(chordText, semitoneOffset, targetKeyText) {
	const normalizedChordText = normalizeChordText(chordText);
	if (!normalizedChordText) return normalizedChordText;
	const [root = "", suffix = "", bassNote = ""] = tokenize(normalizedChordText);
	if (!root) return normalizedChordText;
	const nextRoot = transposePitchClass(root, semitoneOffset, targetKeyText);
	const nextBassNote = bassNote ? transposePitchClass(bassNote, semitoneOffset, targetKeyText) : "";
	return `${nextRoot}${suffix}${nextBassNote ? `/${nextBassNote}` : ""}`;
}
function simplifyChordSymbol(chordText) {
	const normalizedChordText = normalizeChordText(chordText);
	if (!normalizedChordText) return normalizedChordText;
	const [root = "", rawSuffix = ""] = tokenize(normalizedChordText);
	if (!root) return normalizedChordText;
	const normalizedSuffixCandidate = normalizeChordSuffixCandidate(rawSuffix);
	let simplifiedSuffix = rawSuffix;
	if (normalizedSuffixCandidate === "minor") simplifiedSuffix = "m";
	else if (/^m(?:6|7|9|11|13)$/.test(normalizedSuffixCandidate) || normalizedSuffixCandidate === "m7b5" || /^mmaj(?:7|9|11|13|7b5)$/.test(normalizedSuffixCandidate)) simplifiedSuffix = "m";
	return `${root}${simplifiedSuffix}`;
}
/**
* The seven diatonic triads of a song key, tonic first — the chords a song in
* that key most often reaches for (`E` → `E F#m G#m A B C#m D#dim`). Minor
* keys use the natural minor scale. An unparseable key yields `[]`.
*/
function getKeyDiatonicTriads(keyText) {
	const key = parseMainKey(keyText);
	if (!key) return [];
	const triads = key.isMinor ? minorKey(key.tonic).natural.triads : majorKey(key.tonic).triads;
	return Array.from(triads || [], (triad) => String(triad || "")).filter(Boolean);
}
function createChordTransposition(sourceKeyText, targetKeyText) {
	const sourceKey = parseMainKey(sourceKeyText);
	const targetKey = parseMainKey(targetKeyText || sourceKeyText);
	if (!sourceKey || !targetKey) return {
		isActive: false,
		semitoneOffset: 0,
		intervalName: fromSemitones(0),
		targetKeyText: normalizeMusicTheoryText(targetKeyText || sourceKeyText)
	};
	const semitoneOffset = (targetKey.chroma - sourceKey.chroma + 96) % 12;
	return {
		isActive: semitoneOffset !== 0 || sourceKey.raw !== targetKey.raw,
		semitoneOffset,
		intervalName: fromSemitones(semitoneOffset),
		targetKeyText: targetKey.raw
	};
}
function selectKeyValueForChroma(keyValues, chroma, isMinor) {
	return (keyValues || []).map((value) => parseMainKey(value)).filter((parsedKey) => {
		return parsedKey && parsedKey.isMinor === isMinor && parsedKey.chroma === (Number(chroma) % 12 + 12) % 12;
	}).sort((left, right) => {
		const alterationDifference = Math.abs(left.alteration) - Math.abs(right.alteration);
		if (alterationDifference) return alterationDifference;
		const preferredAlterationSign = isMinor ? -1 : 1;
		const leftPreferred = left.alteration === preferredAlterationSign;
		const rightPreferred = right.alteration === preferredAlterationSign;
		if (leftPreferred !== rightPreferred) return Number(rightPreferred) - Number(leftPreferred);
		return left.raw.localeCompare(right.raw);
	})[0]?.raw || "";
}
function getAdjacentChromaticKey(keyText, stepOffset, keyValues) {
	const parsedKey = parseMainKey(keyText);
	if (!parsedKey) return normalizeStructureKeyOption(keyText);
	return selectKeyValueForChroma(keyValues, parsedKey.chroma + Number(stepOffset), parsedKey.isMinor) || parsedKey.raw;
}
function normalizeChordSuffixCandidate(value) {
	const normalizedValue = normalizeChordText(value);
	if (!normalizedValue) return "major";
	if (normalizedValue === "-") return "minor";
	if (/^(?:M|Maj|maj)$/i.test(normalizedValue)) return "major";
	if (/^(?:Min|Minor|min|minor)$/i.test(normalizedValue)) return "minor";
	const leadingMajorMatch = normalizedValue.match(/^M(.+)$/);
	if (leadingMajorMatch) return `maj${leadingMajorMatch[1].toLowerCase()}`;
	const namedMajorMatch = normalizedValue.match(/^Maj(.+)$/i);
	if (namedMajorMatch) return `maj${namedMajorMatch[1].toLowerCase()}`;
	const namedMinorMatch = normalizedValue.match(/^min(?:or)?(.+)$/i);
	if (namedMinorMatch) return `m${namedMinorMatch[1].toLowerCase()}`;
	const mixedMajorMinorMatch = normalizedValue.match(/^m(?:Maj|M)(.+)$/i);
	if (mixedMajorMinorMatch) return `mmaj${mixedMajorMinorMatch[1].toLowerCase()}`;
	if (/^(?:sus|Sus)$/i.test(normalizedValue)) return "sus4";
	if (/^(?:7sus|7Sus)$/i.test(normalizedValue)) return "7sus4";
	if (/^(?:o|O|°)$/u.test(normalizedValue)) return "dim";
	if (/^(?:o7|O7|°7)$/u.test(normalizedValue)) return "dim7";
	if (/^(?:ø|ø7|Ø|Ø7)$/u.test(normalizedValue)) return "m7b5";
	if (/^\+$/u.test(normalizedValue) || /^augmented$/i.test(normalizedValue)) return "aug";
	const augmentedMatch = normalizedValue.match(/^\+(.+)$/);
	if (augmentedMatch) return `aug${augmentedMatch[1].toLowerCase()}`;
	if (normalizedValue === "5") return "major";
	return normalizedValue.toLowerCase();
}
function extractChordDegreeHint(suffixCandidate) {
	const normalizedSuffixCandidate = normalizeChordSuffixCandidate(suffixCandidate);
	if (!normalizedSuffixCandidate) return [];
	if (/^(2|4|5|6|7|9|11|13)$/.test(normalizedSuffixCandidate)) return [normalizedSuffixCandidate];
	const qualityDegreeMatch = normalizedSuffixCandidate.match(/^(?:maj|m|dim|aug|add|no|omit)(2|4|5|6|7|9|11|13)$/);
	if (qualityDegreeMatch) return [qualityDegreeMatch[1]];
	const suspensionMatch = normalizedSuffixCandidate.match(/^sus(2|4)$/);
	if (suspensionMatch) return [suspensionMatch[1]];
	const dominantSuspensionMatch = normalizedSuffixCandidate.match(/^7sus(2|4)$/);
	if (dominantSuspensionMatch) return ["7", dominantSuspensionMatch[1]];
	if (normalizedSuffixCandidate === "m7b5") return ["7"];
	return [];
}
function createDatabaseSuffixCandidates(rawSuffix, chordInfo) {
	const candidates = [];
	function push(value) {
		const normalizedValue = normalizeChordSuffixCandidate(value);
		if (!normalizedValue || candidates.includes(normalizedValue)) return;
		candidates.push(normalizedValue);
	}
	push(rawSuffix);
	if (!normalizeChordText(rawSuffix)) push("major");
	if (chordInfo && !chordInfo.empty) {
		const [, symbolSuffix = ""] = tokenize(chordInfo.symbol || "");
		push(symbolSuffix);
		chordInfo.aliases.forEach(push);
		if (chordInfo.quality === "Major" && chordInfo.intervals.length === 3) push("major");
		if (chordInfo.quality === "Minor" && chordInfo.intervals.length === 3) {
			push("minor");
			push("m");
		}
		if (chordInfo.quality === "Augmented") push("aug");
		if (chordInfo.quality === "Diminished") push("dim");
	}
	push("major");
	return candidates;
}
function createChordDegreeHints(chordKey) {
	const normalizedChordKey = normalizeChordText(chordKey);
	const [root = "", rawSuffix = ""] = tokenize(normalizedChordKey);
	if (!root) return [];
	const chordInfo = get(normalizedChordKey);
	const hints = [];
	function pushHint(value) {
		if (!value || hints.includes(value)) return;
		hints.push(value);
	}
	createDatabaseSuffixCandidates(rawSuffix, chordInfo).forEach((candidate) => {
		extractChordDegreeHint(candidate).forEach(pushHint);
	});
	if (hints.length || !chordInfo || chordInfo.empty) return hints;
	chordInfo.intervals.forEach((intervalName) => {
		const degreeMatch = String(intervalName).match(/^(2|4|6|7|9|11|13)/);
		if (degreeMatch) pushHint(degreeMatch[1]);
	});
	return hints;
}
function createChordDatabaseSearchData(chordKey) {
	const normalizedChordKey = normalizeChordText(chordKey);
	const [root = "", rawSuffix = "", bassRoot = ""] = tokenize(normalizedChordKey);
	if (!root) return null;
	const normalizedRoot = normalizePitchClass(root);
	const rootChroma = getPitchClassChroma(normalizedRoot);
	if (!normalizedRoot || rootChroma == null) return null;
	const normalizedBassRoot = normalizePitchClass(bassRoot);
	const bassPitchClass = normalizedBassRoot ? getPitchClassChroma(normalizedBassRoot) : null;
	const chordInfo = get(normalizedChordKey);
	return {
		bassPitchClass,
		bassRoot: normalizedBassRoot,
		chordInfo,
		datasetRoot: CHORD_DATABASE_ROOTS_BY_CHROMA[rootChroma] || "",
		normalizedChordKey,
		rawSuffix,
		root: normalizedRoot,
		suffixCandidates: createDatabaseSuffixCandidates(rawSuffix, chordInfo)
	};
}
function describeChordKey(chordKey) {
	const normalizedChordKey = normalizeChordText(chordKey);
	if (!normalizedChordKey) return "Chord";
	const chordInfo = get(normalizedChordKey);
	if (!chordInfo.empty && chordInfo.name) return `Chord ${chordInfo.name}`;
	return `Chord ${normalizedChordKey}`;
}
//#endregion
//#region src/plugins/OpenLyric/domain/parser/fences/OLConfig.ts
/**
* The `Config` fields whose value is one line of free text the reader simply
* types — no picker, no list, no notation of their own.
*
* They get the in-place text editor below rather than a popup: a reader who
* never opens the text panel still has to be able to put a title, an artist and
* a copyright line on the song, and those are exactly the fields no menu can
* offer choices for. Every other field already owns a purpose-built control
* (`Key`, `Time`, `Tempo`, `Locales`, `Structure`, `Attachments`,
* `Strumming Patterns`), so none of them appears here.
*/
var EDITABLE_TEXT_CONFIG_FIELD_NAMES = /* @__PURE__ */ new Set([
	"Title",
	"Subtitle",
	"Description",
	"Artist",
	"Copyright",
	"Theme",
	"Genre",
	"Style",
	"Keywords",
	"Year",
	"Melody"
]);
/**
* The field name the Config card prints: the translation the view options
* carry for the field (`helpers.translateLabel`), else what the author wrote.
* Display only — the `data-config-field*` attributes the edit actions read
* keep the notation's own name.
*/
function translateConfigFieldLabel(context, entry) {
	const written = entry.label || entry.key;
	const translated = context.helpers.translateLabel?.(entry.key);
	return translated && translated !== entry.key ? translated : written;
}
function getSingleLineValueEntry(entry) {
	if (!entry || !Array.isArray(entry.values) || entry.values.length !== 1) return null;
	return entry.values[0] || null;
}
function renderEditableKeyField(context, valueEntry) {
	const keyText = String(valueEntry?.text ?? "").trim();
	const keyTitle = keyText ? describeChordKey(keyText) : "Choose key";
	const chordDataAttributes = keyText ? ` data-chord-key="${context.helpers.escapeHtml(keyText)}" data-chord-title="${context.helpers.escapeHtml(keyTitle)}"` : "";
	return [
		"<span class=\"ol-preview-config__field-control\">",
		`<button class="ol-preview-chord ol-preview-config__key-trigger${keyText ? "" : " ol-preview-config__key-trigger--empty"}" type="button" data-preview-action="toggle-config-key-menu" data-config-field="Key" data-config-current-value="${context.helpers.escapeHtml(keyText)}" aria-haspopup="menu" aria-expanded="false" aria-label="${context.helpers.escapeHtml(keyText ? `Change key from ${keyText}` : "Choose key")}" title="${context.helpers.escapeHtml(keyText ? `Change key from ${keyText}` : "Choose key")}"${chordDataAttributes}${context.helpers.getEditorDataAttributes(valueEntry?.lineEntry?.lineNumber, valueEntry?.valueColumn || valueEntry?.lineEntry?.column)}>${context.helpers.escapeHtml(keyText || "Choose key")}</button>`,
		"</span>"
	].join("");
}
function renderEditableTimeField(context, valueEntry) {
	const timeText = String(valueEntry?.text ?? "").trim();
	return [
		"<span class=\"ol-preview-config__field-control\">",
		`<button class="ol-preview-config__time-trigger${timeText ? "" : " ol-preview-config__time-trigger--empty"}" type="button" data-preview-action="toggle-config-time-menu" data-config-field="Time" data-config-current-value="${context.helpers.escapeHtml(timeText)}" aria-haspopup="menu" aria-expanded="false" aria-label="${context.helpers.escapeHtml(timeText ? `Change time signature from ${timeText}` : "Choose time signature")}" title="${context.helpers.escapeHtml(timeText ? `Change time signature from ${timeText}` : "Choose time signature")}"${context.helpers.getEditorDataAttributes(valueEntry?.lineEntry?.lineNumber, valueEntry?.valueColumn || valueEntry?.lineEntry?.column)}>${context.helpers.escapeHtml(timeText || "Choose time")}</button>`,
		"</span>"
	].join("");
}
function getTempoInputValue(valueText) {
	const normalizedValue = String(valueText ?? "").trim();
	if (!normalizedValue) return "";
	const tempoMatch = normalizedValue.match(/^(\d+)(?:\s*bpm)?$/i);
	if (tempoMatch) return String(Number.parseInt(tempoMatch[1], 10));
	return normalizedValue.replace(/\s*bpm$/i, "");
}
function renderEditableTempoField(context, valueEntry) {
	const tempoValueText = getTempoInputValue(valueEntry?.text);
	const hasTempoValue = Boolean(tempoValueText);
	return [
		"<span class=\"ol-preview-config__field-control\">",
		`<button class="ol-preview-config__tempo-trigger${hasTempoValue ? "" : " ol-preview-config__tempo-trigger--empty"}" type="button" data-preview-action="toggle-config-tempo-menu" data-config-field="Tempo" data-config-current-value="${context.helpers.escapeHtml(tempoValueText)}" aria-haspopup="dialog" aria-expanded="false" aria-label="${context.helpers.escapeHtml(hasTempoValue ? `Change tempo from ${tempoValueText} bpm` : "Choose tempo")}" title="${context.helpers.escapeHtml(hasTempoValue ? `Change tempo from ${tempoValueText} bpm` : "Choose tempo")}"${context.helpers.getEditorDataAttributes(valueEntry?.lineEntry?.lineNumber, valueEntry?.valueColumn || valueEntry?.lineEntry?.column)}>${context.helpers.escapeHtml(tempoValueText || "Choose tempo")}</button>`,
		hasTempoValue ? "<span class=\"ol-preview-config__tempo-suffix\" aria-hidden=\"true\">bpm</span>" : "",
		"</span>"
	].join("");
}
/**
* `Locales` as removable chips plus an add action — the Structure field's
* editing model applied to a comma-separated list.
*
* Each chip carries its own tag and source column, so removing one edits that
* locale out of the single `- Locales:` line and a double-click still lands on
* it in the editor. The `+` opens the locale picker (every supported tag the
* line does not already list).
*/
function renderConfigLocalesValue(context, valueEntry) {
	const valueColumn = valueEntry?.valueColumn || valueEntry?.lineEntry?.column || 1;
	const lineNumber = valueEntry?.lineEntry?.lineNumber;
	const localeEntries = parseConfigLocaleEntries(String(valueEntry?.text ?? "")).filter((localeEntry) => localeEntry.text);
	const addActionHtml = [
		"<div class=\"ol-preview-config__locales-action\">",
		`<button class="ol-preview-config__part-action" type="button" data-preview-action="toggle-config-locale-menu" data-config-field="Locales" data-config-current-value="${context.helpers.escapeHtml(localeEntries.map((localeEntry) => localeEntry.text).join(", "))}" aria-haspopup="dialog" aria-expanded="false" aria-label="Add locale" title="Add locale">+</button>`,
		"</div>"
	].join("");
	if (!localeEntries.length) return [
		"<div class=\"ol-preview-config__locales-value ol-preview-config__locales-value--empty\">",
		addActionHtml,
		"</div>"
	].join("");
	return [
		"<div class=\"ol-preview-config__locales-value\">",
		`<div class="ol-preview-config__locales-list">${localeEntries.map((localeEntry) => {
			const localeTag = context.helpers.escapeHtml(localeEntry.text);
			return [
				`<span class="ol-preview-config__locale-item" data-config-locale="${localeTag}"${context.helpers.getEditorDataAttributes(lineNumber, valueColumn + localeEntry.startOffset)}>`,
				`<span class="ol-preview-config__locale-name">${localeTag}</span>`,
				`<button class="ol-preview-config__locale-remove" type="button" data-preview-action="remove-config-locale" data-config-locale="${localeTag}" aria-label="Remove locale ${localeTag}" title="Remove locale"></button>`,
				"</span>"
			].join("");
		}).join("")}</div>`,
		addActionHtml,
		"</div>"
	].join("");
}
function renderAttachmentsAddAction() {
	return [
		"<div class=\"ol-preview-config__attachments-action\">",
		"<button class=\"ol-preview-config__part-action\" type=\"button\" data-preview-action=\"toggle-config-attachment-menu\" aria-haspopup=\"dialog\" aria-expanded=\"false\" aria-label=\"Add attachment\" title=\"Add attachment\">+</button>",
		"</div>"
	].join("");
}
/** A scheme-prefixed URL — `https:`, `file:`, `vscode:`, … — never `javascript:`. */
var ATTACHMENT_URL_RE = /^(?!javascript:)[A-Za-z][A-Za-z0-9+.-]*:\S/i;
/**
* One attachment line as a link. Rendered here rather than through
* `renderInlineText`, whose OL notation reads the `[label]` of a
* `[label](url)` line as a chord, and whose GFM autolinking only knows
* `http(s):`/`www.` — so a `file:///…` line would come out as plain text.
* A line that is not a URL yet (half-typed) still renders as inline text.
*/
function renderConfigAttachmentLink(context, rawValueText) {
	const text = rawValueText.trim();
	const attachment = parseOpenLyricAttachmentLine(text);
	if (!attachment || !ATTACHMENT_URL_RE.test(attachment.link)) return context.helpers.renderInlineText(rawValueText);
	const content = attachment.link === text ? context.helpers.escapeHtml(text) : `${context.helpers.escapeHtml(attachment.title)} <span class="ol-preview-config__attachment-url">(${context.helpers.escapeHtml(attachment.link)})</span>`;
	return `<a class="ol-preview-config__attachment-link" href="${context.helpers.escapeHtml(attachment.link.replace(/ /g, "%20"))}" title="${context.helpers.escapeHtml(attachment.link)}">${content}</a>`;
}
function renderConfigAttachmentsValue(context, entry) {
	const attachmentItems = entry.values.map((value) => {
		const rawValueText = String(value.text ?? "");
		const trimmedValueText = rawValueText.trim();
		const sourceIndex = String(value.sourceIndex ?? "");
		if (!trimmedValueText) return "";
		return `<div class="ol-preview-config__attachment-item" data-attachment-source-index="${context.helpers.escapeHtml(sourceIndex)}"${context.helpers.getEditorDataAttributes(value.lineEntry.lineNumber, value.valueColumn || value.lineEntry.column)}>${renderConfigAttachmentLink(context, rawValueText)}<button class="ol-preview-config__attachment-remove" type="button" data-preview-action="remove-config-attachment" data-attachment-source-index="${context.helpers.escapeHtml(sourceIndex)}" aria-label="Remove attachment ${context.helpers.escapeHtml(trimmedValueText)}" title="Remove attachment"></button></div>`;
	}).filter(Boolean);
	if (!attachmentItems.length) return `<div class="ol-preview-config__attachments-value ol-preview-config__attachments-value--empty">${renderAttachmentsAddAction()}</div>`;
	return [
		"<div class=\"ol-preview-config__attachments-value\">",
		`<div class="ol-preview-config__attachments-list">${attachmentItems.join("")}</div>`,
		renderAttachmentsAddAction(),
		"</div>"
	].join("");
}
function renderMissingConfigAction(context, missingFieldNames) {
	if (!missingFieldNames.length) return "";
	return [
		"<div class=\"ol-preview-config__missing-actions\">",
		`<button class="ol-preview-config__add-button" type="button" data-preview-action="toggle-config-add-menu" data-config-missing-fields="${context.helpers.escapeHtml(missingFieldNames.join("||"))}" aria-haspopup="menu" aria-expanded="false" aria-label="Add missing config field" title="Add missing config field">Add Config</button>`,
		"</div>"
	].join("");
}
/**
* A free-text `Config` field as a value the reader can click.
*
* The rendered value stays exactly what it was — `renderInlineText` output in
* its own span, so a title carrying markdown still renders the same in the
* preview and in every export — and the editing affordance is a pencil beside
* it. Wrapping the rendered value in a button would have been more direct, but
* the inline renderer emits buttons and links of its own, and a button inside a
* button is not markup a browser keeps.
*
* Only the field's source line number travels with the control. The write-back
* (`config-text-editing.ts`) re-reads that line from the document and checks it
* still declares this field before replacing it, so a control left over from
* stale markup edits nothing.
*/
function renderEditableTextField(context, entry, valueEntry) {
	const lineNumber = Number(valueEntry?.lineEntry?.lineNumber) || 0;
	if (!lineNumber) return null;
	const rawValueText = String(valueEntry?.text ?? "");
	const hasValue = Boolean(rawValueText.trim());
	const fieldLabel = entry.label || entry.key;
	const actionLabel = `${hasValue ? "Edit" : "Add"} ${fieldLabel}`;
	const escapedActionLabel = context.helpers.escapeHtml(actionLabel);
	return [
		"<span class=\"ol-preview-config__text-value\">",
		`<span class="ol-preview-config__text-display${hasValue ? "" : " ol-preview-config__text-display--empty"}" data-config-empty-label="${context.helpers.escapeHtml(`Add ${fieldLabel}`)}"${context.helpers.getEditorDataAttributes(lineNumber, valueEntry?.valueColumn || valueEntry?.lineEntry?.column)}>${hasValue ? context.helpers.renderInlineText(rawValueText) : ""}</span>`,
		`<button class="ol-preview-config__text-edit" type="button" data-preview-action="edit-config-text-field" data-config-field="${context.helpers.escapeHtml(entry.key)}" data-config-field-label="${context.helpers.escapeHtml(fieldLabel)}" data-preview-config-line="${lineNumber}" aria-label="${escapedActionLabel}" title="${escapedActionLabel}">${PREVIEW_EDIT_ICON_SVG}</button>`,
		"</span>"
	].join("");
}
function renderEditableConfigValue(context, entry) {
	const valueEntry = getSingleLineValueEntry(entry);
	if (!valueEntry) return null;
	if (entry.key === "Key") return renderEditableKeyField(context, valueEntry);
	if (entry.key === "Time") return renderEditableTimeField(context, valueEntry);
	if (entry.key === "Tempo") return renderEditableTempoField(context, valueEntry);
	if (entry.key === "Locales") return renderConfigLocalesValue(context, valueEntry);
	if (EDITABLE_TEXT_CONFIG_FIELD_NAMES.has(entry.key)) return renderEditableTextField(context, entry, valueEntry);
	return null;
}
var OLConfig = class extends OLFenceDefinition {
	constructor() {
		super({
			className: "OLConfig",
			header: "Config",
			kind: "config",
			description: "Song metadata fence.",
			tokenState: "olConfig",
			required: true
		});
	}
	/**
	* `Config` keeps its per-field controls as the only way to edit it from the
	* preview — see {@link OLFenceDefinition.isPreviewBodyEditable}.
	*/
	isPreviewBodyEditable() {
		return false;
	}
	/**
	* The "Add Lyric" control, in the gap between the `Config` card and the
	* first section card.
	*
	* It sits here — rather than at the end of the sections, or in a panel
	* toolbar — because that gap is where a reader looks once the song's details
	* are filled in and the next thing to do is write a verse. It carries no
	* source position: the section it adds goes after the *last* fence in the
	* document, which only the controller can work out, and only at the moment
	* of the click.
	*
	* Rendered on every markdown-preview surface and revealed by CSS only where
	* the panel advertises a document to write back to, the same rule the
	* section pencils follow.
	*/
	renderPreviewAfterCard(context) {
		const escapedLabel = context.helpers.escapeHtml("Add a lyric section");
		return [
			"<div class=\"ol-preview-add-section\">",
			`<button class="ol-preview-add-section__trigger" type="button" data-preview-action="toggle-add-section-menu" aria-haspopup="dialog" aria-expanded="false" aria-label="${escapedLabel}" title="${escapedLabel}">Add Lyric</button>`,
			"</div>"
		].join("");
	}
	/**
	* What the markdown preview shows for a document with nothing in it: one
	* card with a single "Start a new song" control.
	*
	* `Config` owns it because the song it starts is, first of all, a `Config`
	* fence — the one part the language requires. Like "Add Lyric" it carries no
	* source position (there is nothing to point at yet) and is revealed by CSS
	* only where the panel advertises a document to write back to, so a
	* standalone preview embed keeps rendering a blank document as blank.
	*/
	renderPreviewEmptyDocument(context) {
		const escape = context.helpers.escapeHtml;
		return [
			"<section class=\"ol-preview-start\" data-preview-empty-document=\"true\" aria-label=\"Empty song\">",
			"<p class=\"ol-preview-start__title\">This song is empty</p>",
			`<p class="ol-preview-start__hint" id="ol-preview-start-hint">${escape("Adds the song details — title, artist, key and tempo — and a first verse to write in.")}</p>`,
			`<button class="ol-preview-start__trigger" type="button" data-preview-action="start-song" aria-describedby="ol-preview-start-hint">${escape("Start a new song")}</button>`,
			"</section>"
		].join("");
	}
	/**
	* The `Config` body "Start a new song" writes.
	*
	* Only the required fields, each with a value — an empty single-line field
	* is itself a diagnostic ("<Field> must provide a value on the same line"),
	* and a preview-only reader could not see it. The optional fields stay out
	* rather than arrive empty; the Config card's add-field menu brings them in.
	*
	* `Structure` is required too and must name a declared part, so it names
	* {@link getStarterSectionPartName} — the controller writes that section
	* alongside, and the pair validates clean as written.
	*/
	getStarterBodyLines() {
		return ["- Title: Your Song Title Here", "- Structure: V1"];
	}
	/** The section a started song opens with; the `V1` in its `Structure`. */
	getStarterSectionPartName() {
		return "Verse 1";
	}
	getSnippetBodyLines() {
		return [
			"- Title: Your Song Title Here",
			"- Subtitle:",
			"- Description:",
			"- Artist: Song Artist Here",
			"- Copyright: Copyright Your Name Here",
			"- Locales: en-US",
			"- Key: G",
			"- Tempo: 70bpm",
			"- Time: 4/4",
			"- Theme:",
			"- Structure: IV1CV2CO",
			"- Genre:",
			"- Style:",
			"- Keywords:",
			"- Year:",
			"- Melody:",
			"- Attachments:",
			"- Strumming Patterns:",
			"  $0"
		];
	}
	validateBody(context) {
		context.validators.validateConfigBlock(context.bodyLines, context.startLineNumber, context.markers, context.declaredParts);
	}
	renderPreviewBody(context) {
		const entries = [];
		let currentEntry = null;
		for (const lineEntry of context.lineEntries) {
			const line = lineEntry.text;
			if (lineEntry.isComment || !line.trim()) continue;
			const fieldMatch = line.match(/^\s*-\s*([^:]+):\s*(.*)$/);
			if (fieldMatch) {
				const label = fieldMatch[1].trim();
				const separatorOffset = line.indexOf(":");
				const valueOffset = separatorOffset === -1 ? line.length : separatorOffset + 1;
				const valueIndentLength = line.slice(valueOffset).match(/^\s*/)?.[0].length || 0;
				currentEntry = {
					key: normalizeConfigFieldName(label),
					label,
					lineEntry,
					values: [{
						text: fieldMatch[2],
						lineEntry,
						valueColumn: valueOffset + valueIndentLength + 1,
						sourceIndex: 0
					}]
				};
				entries.push(currentEntry);
				continue;
			}
			if (currentEntry) {
				currentEntry.values.push({
					text: line.trim(),
					lineEntry,
					valueColumn: lineEntry.column,
					sourceIndex: currentEntry.values.length
				});
				continue;
			}
			return context.helpers.renderLineCollection(context.lineEntries);
		}
		const entryMap = new Map(entries.map((entry) => [entry.key, entry]));
		const missingFieldNames = CONFIG_FIELD_NAMES$1.filter((fieldName) => {
			return !entryMap.has(fieldName);
		});
		if (!entries.length) return [
			"<div class=\"ol-preview-config-shell\">",
			context.helpers.renderEmptyBody(),
			renderMissingConfigAction(context, missingFieldNames),
			"</div>"
		].join("");
		const keyText = String(getSingleLineValueEntry(entryMap.get("Key"))?.text ?? "").trim();
		const timeSignatureText = entryMap.get("Time")?.values.map((value) => String(value.text ?? "").trim()).filter(Boolean).join(" ") || "4/4";
		const tempoText = getTempoInputValue(getSingleLineValueEntry(entryMap.get("Tempo"))?.text);
		const strummingPatternPreviewContext = entryMap.has("Strumming Patterns") ? context.helpers.createStrummingPatternPreviewContextFromConfigBody(context.body, { sourceLocation: context.sourceLocation }) : null;
		return [
			"<div class=\"ol-preview-config-shell\">",
			"<dl class=\"ol-preview-config\">",
			...entries.flatMap((entry) => {
				const isAttachments = entry.key === "Attachments";
				const isStrummingPatterns = entry.key === "Strumming Patterns";
				const isMultiline = isStrummingPatterns || isAttachments || entry.values.length > 1;
				const valueHtml = renderEditableConfigValue(context, entry) ?? (isAttachments ? renderConfigAttachmentsValue(context, entry) : entry.key === "Structure" ? context.helpers.renderStructureValue(entry.values) : isStrummingPatterns ? context.helpers.renderConfigStrummingPatternValue(entry.values, timeSignatureText, {
					keyText,
					patterns: strummingPatternPreviewContext?.patterns,
					tempoText
				}) : entry.values.map((value) => {
					const rawValueText = String(value.text ?? "");
					const trimmedValueText = rawValueText.trim();
					const renderedValueText = entry.key === "Key" && trimmedValueText ? context.helpers.renderInlineText(`[${trimmedValueText}]`) : context.helpers.renderInlineText(rawValueText);
					return `<span${context.helpers.getEditorDataAttributes(value.lineEntry.lineNumber, value.valueColumn || value.lineEntry.column)}>${renderedValueText}</span>`;
				}).join("<br>"));
				return [
					`<div class="ol-preview-config__entry${isMultiline ? " ol-preview-config__entry--stacked" : " ol-preview-config__entry--inline"}">`,
					`<dt class="ol-preview-config__key${isStrummingPatterns ? " ol-preview-config__key--patterns" : ""}"${context.helpers.getEditorDataAttributes(entry.lineEntry.lineNumber, entry.lineEntry.column)}>${context.helpers.escapeHtml(translateConfigFieldLabel(context, entry))}:</dt>`,
					`<dd class="ol-preview-config__value${isStrummingPatterns ? " ol-preview-config__value--patterns" : ""}${entry.key === "Structure" ? " ol-preview-config__value--structure" : ""}"${context.helpers.getEditorDataAttributes(entry.lineEntry.lineNumber, entry.lineEntry.column)}>${valueHtml}</dd>`,
					"</div>"
				];
			}),
			"</dl>",
			renderMissingConfigAction(context, missingFieldNames),
			"</div>"
		].join("");
	}
};
//#endregion
//#region src/plugins/OpenLyric/domain/parser/fences/OLFinalChorus.ts
var OLFinalChorus = class extends OLLyricFence {
	constructor() {
		super({
			className: "OLFinalChorus",
			header: "Final-Chorus",
			description: "Lyric section fence."
		});
	}
};
//#endregion
//#region src/plugins/OpenLyric/domain/edit-distance.ts
/**
* Near-miss matching for names a song spells — fence headers, Config fields —
* so a diagnostic can say "Did you mean …?".
*/
/**
* A name as typed and as defined, compared: no case, spaces, underscores or
* hyphens — `pre chorus` and `Pre-Chorus`, `title` and `Title` meet.
*/
function toLooseNameKey(value) {
	return String(value ?? "").toLowerCase().replace(/[\s_-]+/gu, "");
}
/**
* How many single-letter edits turn `left` into `right`, a swap of two
* neighbours counting as one (`chrous` → `chorus` is 1).
*/
function getEditDistance(left, right) {
	const rows = Array.from({ length: left.length + 1 }, (_, row) => Array.from({ length: right.length + 1 }, (_, column) => row === 0 ? column : column === 0 ? row : 0));
	for (let row = 1; row <= left.length; row += 1) for (let column = 1; column <= right.length; column += 1) {
		const cost = left[row - 1] === right[column - 1] ? 0 : 1;
		rows[row][column] = Math.min(rows[row - 1][column] + 1, rows[row][column - 1] + 1, rows[row - 1][column - 1] + cost);
		if (row > 1 && column > 1 && left[row - 1] === right[column - 2] && left[row - 2] === right[column - 1]) rows[row][column] = Math.min(rows[row][column], rows[row - 2][column - 2] + 1);
	}
	return rows[left.length][right.length];
}
/**
* The name in `candidates` that `typed` was most likely meant to be — within
* one edit for a name of four letters or fewer, two for a longer one, after
* {@link toLooseNameKey} — or `''` when none is that close. Ties go to the
* earlier candidate.
*/
function findClosestName(typed, candidates) {
	const wanted = toLooseNameKey(typed);
	if (!wanted) return "";
	let closest = "";
	let closestDistance = Infinity;
	for (const candidate of candidates) {
		const distance = getEditDistance(wanted, toLooseNameKey(candidate));
		if (distance <= (String(candidate).length <= 4 ? 1 : 2) && distance < closestDistance) {
			closest = candidate;
			closestDistance = distance;
		}
	}
	return closest;
}
//#endregion
//#region src/plugins/OpenLyric/domain/parser/fences/OLFenceRegistry.ts
var UNSUPPORTED_PART_MESSAGE = "Unsupported ol part. Use Config, Intro, Instrumental, Interlude, Turnaround, lyric sections, Breakdown, Vamp, or Solo.";
var OLFenceRegistry = class {
	constructor(definitions) {
		this.definitions = definitions.slice();
		this.definitionsByHeader = new Map(this.definitions.map((definition) => [definition.header, definition]));
		this.headerPrefixDefinitions = this.definitions.slice().sort((left, right) => right.header.length - left.header.length);
	}
	getDefinitions() {
		return this.definitions.slice();
	}
	findByHeader(header) {
		return this.definitionsByHeader.get(header) || null;
	}
	parseHeader(info) {
		for (const definition of this.definitions) {
			const parsedHeader = definition.parseHeader(info);
			if (parsedHeader) return parsedHeader;
		}
		return null;
	}
	getFenceBlockKind(info) {
		return this.parseHeader(info)?.kind || "unknown";
	}
	getRequiredDeclaredPartNames() {
		return this.definitions.filter((definition) => definition.required).map((definition) => definition.header);
	}
	getSnippetDefinitions() {
		const seenHeaders = /* @__PURE__ */ new Set();
		return this.definitions.flatMap((definition) => definition.getSnippetDefinitions()).filter(({ header }) => {
			if (seenHeaders.has(header)) return false;
			seenHeaders.add(header);
			return true;
		});
	}
	findHeaderPrefix(info) {
		for (const definition of this.headerPrefixDefinitions) {
			if (!info.startsWith(definition.header)) continue;
			const nextCharacter = info[definition.header.length];
			if (!nextCharacter || /\s|\(/.test(nextCharacter)) return definition;
		}
		return null;
	}
	getFenceHeaderError(info) {
		const configDefinition = this.findByHeader("Config");
		if (info === "config") return "Use ol:Config. Lowercase ol:config is not supported.";
		if (configDefinition && info.startsWith(configDefinition.header) && !configDefinition.parseHeader(info)) return "Config fences cannot be numbered or suffixed.";
		const sectionDefinition = this.findHeaderPrefix(info);
		if (sectionDefinition) {
			const indexMatch = info.slice(sectionDefinition.header.length).trimStart().match(/^(\d+)/);
			if (indexMatch) {
				if (!sectionDefinition.allowsNumbering) return `${sectionDefinition.header} fences cannot be numbered.`;
				if (indexMatch[1].startsWith("0")) return "Section indexes must start at 1.";
			}
		}
		const suggestion = this.suggestHeader(info);
		return suggestion ? `Unsupported ol part. Did you mean ol:${suggestion}?` : UNSUPPORTED_PART_MESSAGE;
	}
	/**
	* The header to put in place of an `info` that is not one — `Config` for
	* `config`, the {@link suggestHeader} match otherwise — or `''` when there
	* is none to offer (a valid header, a numbered `Config`, a bad index).
	*/
	getFenceHeaderFix(info) {
		if (this.parseHeader(info)) return "";
		if (info === "config") return "Config";
		return this.getFenceHeaderError(info).startsWith("Unsupported ol part. Did you mean ol:") ? this.suggestHeader(info) : "";
	}
	/**
	* The header `info` was most likely meant to be — `Verse 2` for `Vers 2`,
	* `Pre-Chorus 1` for `pre chorus 1` — or `''` when no header is close. A
	* header of four letters or fewer allows one slip, a longer one two.
	*/
	suggestHeader(info) {
		const match = String(info ?? "").trim().match(/^(.*?)(?:\s*([1-9]\d*))?$/u);
		const wanted = toLooseNameKey(match?.[1]);
		const index = match?.[2];
		if (!wanted) return "";
		let closest = null;
		let closestDistance = Infinity;
		for (const definition of this.definitions) {
			const distance = getEditDistance(wanted, toLooseNameKey(definition.header));
			if (distance <= (definition.header.length <= 4 ? 1 : 2) && distance < closestDistance) {
				closest = definition;
				closestDistance = distance;
			}
		}
		if (!closest) return "";
		const suggestion = index && closest.allowsNumbering ? `${closest.header} ${index}` : closest.header;
		return suggestion === String(info ?? "").trim() ? "" : suggestion;
	}
};
//#endregion
//#region src/plugins/OpenLyric/domain/parser/fences/OLInstrumentalFence.ts
var OLInstrumentalFence = class extends OLFenceDefinition {
	constructor(options) {
		super({
			...options,
			kind: "instrumental",
			tokenState: "olInstrumental"
		});
	}
	validateBody(context) {
		context.validators.validateDirectiveBlock(context.bodyLines, context.startLineNumber, context.markers, this.header, context.directivePatterns.instrumental, "{c: Piano + Pads }");
	}
	getPreviewChordInsertStyle() {
		return "progression";
	}
	renderPreviewBody(context) {
		return context.helpers.renderChordProgressionLineCollection(context.lineEntries);
	}
};
//#endregion
//#region src/plugins/OpenLyric/domain/parser/fences/OLInstrumental.ts
var OLInstrumental = class extends OLInstrumentalFence {
	constructor() {
		super({
			className: "OLInstrumental",
			header: "Instrumental",
			description: "Instrumental section fence.",
			allowsNumbering: true
		});
	}
};
//#endregion
//#region src/plugins/OpenLyric/domain/parser/fences/OLInterlude.ts
var OLInterlude = class extends OLInstrumentalFence {
	constructor() {
		super({
			className: "OLInterlude",
			header: "Interlude",
			description: "Instrumental section fence.",
			allowsNumbering: true
		});
	}
};
//#endregion
//#region src/plugins/OpenLyric/domain/parser/fences/OLIntro.ts
var OLIntro = class extends OLFenceDefinition {
	constructor() {
		super({
			className: "OLIntro",
			header: "Intro",
			kind: "intro",
			description: "Lyric or progression section fence.",
			tokenState: "olIntro"
		});
	}
	validateBody(context) {
		context.validators.validateMixedBlock(context.bodyLines, context.startLineNumber, context.markers, this.header);
	}
	getPreviewChordInsertStyle() {
		return "mixed";
	}
	renderPreviewBody(context) {
		return context.helpers.renderMixedLineCollection(context.lineEntries);
	}
};
//#endregion
//#region src/plugins/OpenLyric/domain/parser/fences/OLNote.ts
var OLNote = class extends OLLyricFence {
	constructor() {
		super({
			className: "OLNote",
			header: "Note",
			description: "Lyric section fence.",
			allowsNumbering: true
		});
	}
};
//#endregion
//#region src/plugins/OpenLyric/domain/parser/fences/OLOutro.ts
var OLOutro = class extends OLFenceDefinition {
	constructor() {
		super({
			className: "OLOutro",
			header: "Outro",
			kind: "outro",
			description: "Lyric or progression section fence.",
			tokenState: "olOutro"
		});
	}
	validateBody(context) {
		context.validators.validateMixedBlock(context.bodyLines, context.startLineNumber, context.markers, this.header);
	}
	getPreviewChordInsertStyle() {
		return "mixed";
	}
	renderPreviewBody(context) {
		return context.helpers.renderMixedLineCollection(context.lineEntries);
	}
};
//#endregion
//#region src/plugins/OpenLyric/domain/parser/fences/OLPostChorus.ts
var OLPostChorus = class extends OLLyricFence {
	constructor() {
		super({
			className: "OLPostChorus",
			header: "Post-Chorus",
			allowsNumbering: true,
			description: "Lyric section fence."
		});
	}
};
//#endregion
//#region src/plugins/OpenLyric/domain/parser/fences/OLPreChorus.ts
var OLPreChorus = class extends OLLyricFence {
	constructor() {
		super({
			className: "OLPreChorus",
			header: "Pre-Chorus",
			allowsNumbering: true,
			description: "Lyric section fence."
		});
	}
};
//#endregion
//#region src/plugins/OpenLyric/domain/parser/fences/OLRefrain.ts
var OLRefrain = class extends OLLyricFence {
	constructor() {
		super({
			className: "OLRefrain",
			header: "Refrain",
			allowsNumbering: true,
			description: "Lyric section fence."
		});
	}
};
//#endregion
//#region src/plugins/OpenLyric/domain/parser/fences/OLSolo.ts
var OLSolo = class extends OLFreeTextFence {
	constructor() {
		super({
			className: "OLSolo",
			header: "Solo",
			description: "Free-text section fence.",
			allowsNumbering: true
		});
	}
};
//#endregion
//#region src/plugins/OpenLyric/domain/parser/fences/OLTag.ts
var OLTag = class extends OLLyricFence {
	constructor() {
		super({
			className: "OLTag",
			header: "Tag",
			description: "Lyric section fence.",
			allowsNumbering: true
		});
	}
};
//#endregion
//#region src/plugins/OpenLyric/domain/parser/fences/OLTurnaround.ts
/**
* The short connective passage that carries one section into the next.
*
* Distinct from `Instrumental` on purpose: chart convention treats an
* instrumental as a whole section without lyrics, while a turnaround (`TA` in
* chart shorthand) is the in-between music joining two sections. It is usually
* played, occasionally sung over, so it takes the same per-line reading as
* `Intro` and `Outro` rather than being progression-only.
*/
var OLTurnaround = class extends OLFenceDefinition {
	constructor() {
		super({
			className: "OLTurnaround",
			header: "Turnaround",
			kind: "turnaround",
			description: "Connective passage between sections.",
			tokenState: "olTurnaround",
			allowsNumbering: true
		});
	}
	validateBody(context) {
		context.validators.validateMixedBlock(context.bodyLines, context.startLineNumber, context.markers, this.header);
	}
	getPreviewChordInsertStyle() {
		return "mixed";
	}
	renderPreviewBody(context) {
		return context.helpers.renderMixedLineCollection(context.lineEntries);
	}
};
//#endregion
//#region src/plugins/OpenLyric/domain/parser/fences/OLVamp.ts
var OLVamp = class extends OLFreeTextFence {
	constructor() {
		super({
			className: "OLVamp",
			header: "Vamp",
			description: "Free-text section fence."
		});
	}
};
//#endregion
//#region src/plugins/OpenLyric/domain/parser/fences/OLVerse.ts
var OLVerse = class extends OLLyricFence {
	constructor() {
		super({
			className: "OLVerse",
			header: "Verse",
			description: "Lyric section fence.",
			allowsNumbering: true
		});
	}
};
var definitions = [
	new OLConfig(),
	new OLIntro(),
	new OLFinalChorus(),
	new OLPreChorus(),
	new OLPostChorus(),
	new OLRefrain(),
	new OLBridge(),
	new OLChorus(),
	new OLVerse(),
	new OLNote(),
	new OLTag(),
	new OLTurnaround(),
	new OLOutro(),
	new OLInstrumental(),
	new OLInterlude(),
	new OLBreakdown(),
	new OLVamp(),
	new OLSolo()
];
var registry = new OLFenceRegistry(definitions);
Object.fromEntries(definitions.map((definition) => [definition.className, definition]));
registry.getDefinitions();
function parseFenceHeader(info) {
	return registry.parseHeader(info);
}
function getFenceHeaderError(info) {
	return registry.getFenceHeaderError(info);
}
function getFenceHeaderFix(info) {
	return registry.getFenceHeaderFix(info);
}
function getRequiredDeclaredPartNames() {
	return registry.getRequiredDeclaredPartNames();
}
//#endregion
//#region src/plugins/OpenLyric/domain/structure.ts
var STRUCTURE_TOKEN_DEFINITIONS = [
	{
		code: "I",
		header: "Intro",
		allowsNumbering: false
	},
	{
		code: "V",
		header: "Verse",
		allowsNumbering: true
	},
	{
		code: "N",
		header: "Note",
		allowsNumbering: true
	},
	{
		code: "P",
		header: "Pre-Chorus",
		allowsNumbering: true
	},
	{
		code: "C",
		header: "Chorus",
		allowsNumbering: true
	},
	{
		code: "X",
		header: "Post-Chorus",
		allowsNumbering: true
	},
	{
		code: "F",
		header: "Final-Chorus",
		allowsNumbering: false
	},
	{
		code: "B",
		header: "Bridge",
		allowsNumbering: true
	},
	{
		code: "IS",
		header: "Instrumental",
		allowsNumbering: true
	},
	{
		code: "L",
		header: "Interlude",
		allowsNumbering: true
	},
	{
		code: "D",
		header: "Breakdown",
		allowsNumbering: true
	},
	{
		code: "R",
		header: "Refrain",
		allowsNumbering: true
	},
	{
		code: "T",
		header: "Tag",
		allowsNumbering: true
	},
	{
		code: "TU",
		header: "Turnaround",
		allowsNumbering: true
	},
	{
		code: "A",
		header: "Vamp",
		allowsNumbering: false
	},
	{
		code: "S",
		header: "Solo",
		allowsNumbering: true
	},
	{
		code: "O",
		header: "Outro",
		allowsNumbering: false
	}
];
var STRUCTURE_TOKEN_DEFINITIONS_BY_LENGTH = [...STRUCTURE_TOKEN_DEFINITIONS].sort((left, right) => right.code.length - left.code.length);
Math.max(...STRUCTURE_TOKEN_DEFINITIONS.map((definition) => definition.code.length));
var STRUCTURE_SYNTAX_EXAMPLE = "IV1x2CV1V2CO";
var STRUCTURE_CODE_LIST = STRUCTURE_TOKEN_DEFINITIONS.map((definition) => definition.code).join(", ");
function matchStructureDefinition(source, offset) {
	return STRUCTURE_TOKEN_DEFINITIONS_BY_LENGTH.find((definition) => source.startsWith(definition.code, offset)) || null;
}
function createStructureError(startOffset, endOffset, message) {
	return {
		startOffset,
		endOffset: Math.max(startOffset + 1, endOffset),
		message
	};
}
function formatStructureStepLabel(step) {
	if (!step) return "";
	const partName = step.partName || step.partText || "";
	return step.repeatText ? `${partName} (${step.repeatText})` : partName;
}
function findAdjacentDuplicateStructureError(steps) {
	if (!Array.isArray(steps) || steps.length < 2) return null;
	for (let index = 1; index < steps.length; index += 1) {
		const previousStep = steps[index - 1];
		const step = steps[index];
		if (!previousStep || !step || previousStep.partName !== step.partName) continue;
		return createStructureError(step.startOffset, step.endOffset, `Structure cannot place ${step.partName} twice in a row. Increase the previous token's repeat count instead.`);
	}
	return null;
}
function parseStructureValue(value) {
	const source = String(value ?? "").trim();
	if (!source) return {
		text: source,
		steps: [],
		error: null
	};
	const steps = [];
	let offset = 0;
	while (offset < source.length) {
		if (/\s/.test(source[offset])) return {
			text: source,
			steps,
			error: createStructureError(offset, offset + 1, `Structure must use compact codes like ${STRUCTURE_SYNTAX_EXAMPLE}.`)
		};
		const definition = matchStructureDefinition(source, offset);
		if (!definition) return {
			text: source,
			steps,
			error: createStructureError(offset, offset + 1, `Unknown structure code. Use ${STRUCTURE_CODE_LIST}.`)
		};
		const stepStartOffset = offset;
		offset += definition.code.length;
		let indexText = "";
		const indexMatch = source.slice(offset).match(/^\d+/);
		if (indexMatch) {
			indexText = indexMatch[0];
			if (!definition.allowsNumbering) return {
				text: source,
				steps,
				error: createStructureError(offset, offset + indexText.length, `${definition.header} cannot be numbered in Structure.`)
			};
			if (indexText.startsWith("0")) return {
				text: source,
				steps,
				error: createStructureError(offset, offset + indexText.length, "Section indexes must start at 1.")
			};
			offset += indexText.length;
		}
		let repeatText = "";
		if (source[offset] === "x") {
			const repeatMatch = source.slice(offset).match(/^x(\d+)/);
			if (!repeatMatch) return {
				text: source,
				steps,
				error: createStructureError(offset, offset + 1, "Repeat suffix must use compact format x2.")
			};
			const repeatCount = repeatMatch[1];
			if (repeatCount.startsWith("0")) return {
				text: source,
				steps,
				error: createStructureError(offset, offset + repeatMatch[0].length, "Repeat counts must start at 1.")
			};
			repeatText = `${repeatCount}x`;
			offset += repeatMatch[0].length;
		}
		const partText = indexText ? `${definition.header} ${indexText}` : definition.header;
		const parsedHeader = parseFenceHeader(partText);
		steps.push({
			code: definition.code,
			definition,
			displayText: repeatText ? `${partText} (${repeatText})` : partText,
			endOffset: offset,
			header: definition.header,
			indexText,
			parsedHeader,
			partName: parsedHeader?.partName || partText,
			partText,
			rawText: source.slice(stepStartOffset, offset),
			repeatText,
			startOffset: stepStartOffset
		});
	}
	return {
		text: source,
		steps,
		error: null
	};
}
//#endregion
//#region src/plugins/OpenLyric/document/validation.ts
var { CONFIG_ENUM_FIELD_VALUES, CONFIG_FIELD_NAMES, CONFIG_FIELD_MATCH_NAMES, CONFIG_MULTILINE_FIELD_NAMES, CONFIG_PATTERN_FIELD_MESSAGES, CONFIG_PATTERN_FIELD_VALUES, CONFIG_REQUIRED_FIELD_NAMES } = grammar;
/** Every field name, in canonical order, as the message lists them. */
var UNSUPPORTED_CONFIG_FIELD_MESSAGE = `Unsupported config field. Use ${CONFIG_FIELD_NAMES.slice(0, -1).join(", ")}, or ${CONFIG_FIELD_NAMES[CONFIG_FIELD_NAMES.length - 1]}.`;
/**
* The Config field an unknown one was most likely meant to be — `Title` for
* `title` or `Tittle`, `Structure` for `Strucure` — or `''`. Never one of
* `takenFieldNames` (canonical names): the fence already has that field, so
* the fix would only trade the typo for a duplicate.
*/
function suggestConfigFieldName(rawFieldName, takenFieldNames = /* @__PURE__ */ new Set()) {
	const typed = String(rawFieldName ?? "").trim();
	const suggestion = normalizeConfigFieldName(findClosestName(typed, CONFIG_FIELD_MATCH_NAMES.filter((name) => !takenFieldNames.has(normalizeConfigFieldName(name)))));
	return suggestion && suggestion !== typed ? suggestion : "";
}
/** `Key` values by their spelling with case, spaces and ♯/♭ folded away. */
var CONFIG_KEY_VALUES_BY_FOLDED_SPELLING = new Map(CONFIG_ENUM_FIELD_VALUES.Key.map((key) => [key.toLowerCase(), key]));
/**
* The value a `Key`, `Time` or `Tempo` entry was plainly meant to hold, or
* `''` when there is no single one: `g` → `G`, `f♯m` → `F#m`, `4 / 4` →
* `4/4`, `70 bpm` → `70bpm`. A Key ending in a capital `M` gets none, since
* `GM` may mean G major as well as G minor.
*/
function suggestConfigFieldValue(fieldName, valueText) {
	const value = String(valueText ?? "");
	if (fieldName === "Key") return /M$/u.test(value) ? "" : CONFIG_KEY_VALUES_BY_FOLDED_SPELLING.get(value.replace(/\s+/gu, "").replace(/♯/gu, "#").replace(/♭/gu, "b").toLowerCase()) || "";
	if (fieldName === "Time") {
		const time = value.replace(/\s+/gu, "");
		return CONFIG_ENUM_FIELD_VALUES.Time.includes(time) ? time : "";
	}
	if (fieldName === "Tempo") {
		const beats = value.match(/^0*([1-9]\d*)\s*(?:bpm)?$/iu)?.[1];
		return beats ? `${beats}bpm` : "";
	}
	return "";
}
/**
* A Config value marker (it starts at the field's `:`) with the fix that
* writes `value` there, when there is one.
*/
function withConfigValueFix(marker, value) {
	return withMarkerFix(marker, value && `: ${value}`, `Change to ${value}`);
}
var CONFIG_ENTRY_RE$3 = new RegExp(`^\\s*-\\s*(${CONFIG_FIELD_MATCH_NAMES.map(escapeRegex).join("|")})\\s*:(.*)$`);
var CONFIG_FIELD_LINE_RE$3 = /^\s*-\s*([^:]+?)(?::(.*))?$/;
var ATTACHMENT_URL_SCHEME_SOURCE$1 = String.raw`[A-Za-z][A-Za-z0-9+.-]*:\/\/`;
var ATTACHMENT_SOURCE_URL_SOURCE$1 = String.raw`(?:${ATTACHMENT_URL_SCHEME_SOURCE$1}\S[^\r\n]*)`;
var ATTACHMENT_MARKDOWN_URL_SOURCE$1 = String.raw`(?:${ATTACHMENT_URL_SCHEME_SOURCE$1}\S[^\r\n)]*)`;
var ATTACHMENT_VALUE_SOURCE$1 = String.raw`(?:${ATTACHMENT_SOURCE_URL_SOURCE$1}|\[[^\]\r\n]+\]\(${ATTACHMENT_MARKDOWN_URL_SOURCE$1}\))`;
var ATTACHMENT_VALUE_RE$1 = new RegExp(`^${ATTACHMENT_VALUE_SOURCE$1}$`);
var STRUMMING_PATTERN_MESSAGE = "Strumming Patterns must use only d, D, v, V, u, U, ^, x, X, 1, *, +, -, _, ., 0, bar separators (|), and spaces or tabs.";
var STRUMMING_PATTERN_CONTINUATION_MESSAGE = "Strumming Patterns continuation lines must start with spaces or tabs and use only d, D, v, V, u, U, ^, x, X, 1, *, +, -, _, ., 0, bar separators (|), and spaces or tabs.";
var MARKER_SEVERITY_ERROR_FALLBACK = 8;
function getErrorMarkerSeverity() {
	return globalThis.monaco?.MarkerSeverity?.Error ?? MARKER_SEVERITY_ERROR_FALLBACK;
}
/**
* `marker` with the edit that fixes it: put `text` in place of the marker's
* range. Editors offer it as a quick fix (`getMarkdownOlMarkerFixes`); the
* MCP's `validate_song` hands it to an agent.
*/
function withMarkerFix(marker, text, title = `Change to ${text}`) {
	if (marker && text) marker.fix = {
		title,
		text
	};
	return marker;
}
function createMarker(lineNumber, startColumn, endColumn, message, severity = getErrorMarkerSeverity()) {
	return {
		severity,
		source: LANGUAGE_ID,
		message,
		startLineNumber: lineNumber,
		startColumn: Math.max(1, startColumn),
		endLineNumber: lineNumber,
		endColumn: Math.max(startColumn + 1, endColumn)
	};
}
function createDocumentMarker(lines, message, severity = getErrorMarkerSeverity(), allowZwspSeparators = true) {
	const firstContentLineIndex = lines.findIndex((line) => trimSpaceLikeText(line, allowZwspSeparators));
	const lineIndex = firstContentLineIndex === -1 ? 0 : firstContentLineIndex;
	const line = lines[lineIndex] || "";
	const startColumn = trimSpaceLikeText(line, allowZwspSeparators) ? getNonWhitespaceColumn(line, allowZwspSeparators) : 1;
	const endColumn = trimSpaceLikeText(line, allowZwspSeparators) ? line.length + 1 : 2;
	return createMarker(lineIndex + 1, startColumn, endColumn, message, severity);
}
function getNonWhitespaceColumn(line, allowZwspSeparators = true) {
	let index = 0;
	while (index < line.length && isSpaceLikeCharacter(line[index], allowZwspSeparators)) index += 1;
	return index >= line.length ? 1 : index + 1;
}
function isCommentLine$1(line, allowZwspSeparators = true) {
	return trimSpaceLikeStart(line, allowZwspSeparators).startsWith("//");
}
function buildJoinedText(lines, startLineNumber, allowZwspSeparators = true) {
	let text = "";
	const positions = [];
	let hasContent = false;
	lines.forEach((line, index) => {
		if (isCommentLine$1(line, allowZwspSeparators)) return;
		const trimmed = trimSpaceLikeText(line, allowZwspSeparators);
		if (!trimmed) return;
		if (hasContent) {
			text += " ";
			positions.push({
				lineNumber: startLineNumber + index,
				column: 1
			});
		}
		const startColumn = getNonWhitespaceColumn(line, allowZwspSeparators);
		for (let offset = 0; offset < trimmed.length; offset += 1) {
			text += trimmed[offset];
			positions.push({
				lineNumber: startLineNumber + index,
				column: startColumn + offset
			});
		}
		hasContent = true;
	});
	return {
		text,
		positions
	};
}
function pushJoinedMarker(markers, joined, startOffset, endOffset, message, severity = getErrorMarkerSeverity()) {
	if (!joined.positions.length) return;
	const startIndex = Math.min(Math.max(0, startOffset), joined.positions.length - 1);
	const endIndex = Math.min(Math.max(startIndex, endOffset - 1), joined.positions.length - 1);
	const start = joined.positions[startIndex];
	const end = joined.positions[endIndex];
	const marker = {
		severity,
		source: LANGUAGE_ID,
		message,
		startLineNumber: start.lineNumber,
		startColumn: start.column,
		endLineNumber: end.lineNumber,
		endColumn: end.column + 1
	};
	markers.push(marker);
	return marker;
}
function skipSpaces(text, startOffset, allowZwspSeparators = true) {
	let offset = startOffset;
	while (offset < text.length && isSpaceLikeCharacter(text[offset], allowZwspSeparators)) offset += 1;
	return offset;
}
function findTokenBoundary(text, startOffset, allowZwspSeparators = true) {
	let offset = startOffset;
	while (offset < text.length) {
		if (isSpaceLikeCharacter(text[offset], allowZwspSeparators)) break;
		offset += 1;
	}
	return Math.max(startOffset + 1, offset);
}
function findClosingBrace(text, startOffset) {
	const closingIndex = text.indexOf("}", startOffset + 1);
	return closingIndex === -1 ? text.length : closingIndex + 1;
}
/** The annotation `[Gxyz]` was most likely meant to be (`[G]`), or `''`. */
function suggestChordAnnotation(annotation, allowZwspSeparators = true) {
	const innerText = trimSpaceLikeText(annotation.slice(1, -1), allowZwspSeparators);
	const suggestedChord = innerText.match(CHORD_SYMBOL_RE)?.[0] || "";
	return suggestedChord && suggestedChord !== innerText ? `[${suggestedChord}]` : "";
}
function getChordAnnotationMessage(annotation, allowZwspSeparators = true) {
	const suggestion = suggestChordAnnotation(annotation, allowZwspSeparators);
	return suggestion ? `Invalid chord annotation. Try ${suggestion}.` : "Invalid chord annotation.";
}
/** A whole token that is one chord symbol, and nothing else. */
var BARE_CHORD_SYMBOL_RE = new RegExp(`${CHORD_SYMBOL_RE.source}$`, "u");
/**
* The chord a progression token was most likely meant to be: `G` for `[G]`
* (a progression takes no brackets), `Em` for `em`, `Bm` for `Hm` (German
* notation's B), or `''` when it is none of those.
*/
function suggestProgressionChord(token) {
	const bare = token.replace(/^\[(.*)\]$/u, "$1");
	const capitalized = bare.charAt(0).toUpperCase() + bare.slice(1);
	return [
		bare,
		capitalized,
		capitalized.replace(/^H/u, "B")
	].find((candidate) => candidate !== token && BARE_CHORD_SYMBOL_RE.test(candidate)) || "";
}
/** What a token a progression cannot read is told: its text, and the fix. */
function getProgressionTokenMessage(token, sectionLabel) {
	const prefix = `Invalid ${sectionLabel.toLowerCase()} token "${token}".`;
	const suggestion = suggestProgressionChord(token);
	return suggestion ? `${prefix} Try ${suggestion}.` : `${prefix} Use chords, | bars and (2x) repeats.`;
}
function validateStructureValue(valueText, lineNumber, valueColumn, markers, declaredParts) {
	const parsedStructure = parseStructureValue(valueText);
	if (parsedStructure.error) {
		markers.push(createMarker(lineNumber, valueColumn + parsedStructure.error.startOffset, valueColumn + parsedStructure.error.endOffset, parsedStructure.error.message));
		return;
	}
	const adjacentDuplicateError = findAdjacentDuplicateStructureError(parsedStructure.steps);
	if (adjacentDuplicateError) {
		markers.push(createMarker(lineNumber, valueColumn + adjacentDuplicateError.startOffset, valueColumn + adjacentDuplicateError.endOffset, adjacentDuplicateError.message));
		return;
	}
	parsedStructure.steps.forEach((step) => {
		if (declaredParts.has(step.partName)) return;
		markers.push(createMarker(lineNumber, valueColumn + step.startOffset, valueColumn + step.endOffset, `Structure references undeclared ol part. ${step.partName} is not declared.`));
	});
}
/**
* Mark every problem in a `Locales` value: an empty entry, a tag outside the
* supported list, and a tag listed twice.
*
* Each marker covers only the offending tag rather than the whole value — a
* three-locale list with one typo should squiggle the typo.
*/
function validateLocalesValue(valueText, lineNumber, valueColumn, markers, allowZwspSeparators = true) {
	const localeEntries = parseConfigLocaleEntries(valueText, allowZwspSeparators);
	const seenLocaleTags = /* @__PURE__ */ new Set();
	localeEntries.forEach((localeEntry) => {
		const startColumn = valueColumn + localeEntry.startOffset;
		const endColumn = Math.max(startColumn + 1, valueColumn + localeEntry.endOffset);
		if (!localeEntry.text) {
			markers.push(createMarker(lineNumber, startColumn, endColumn, "Locales must be a comma-separated list of locales with no empty entry."));
			return;
		}
		if (!isSupportedConfigLocale(localeEntry.text)) {
			const canonicalLocale = findCanonicalConfigLocale(localeEntry.text);
			markers.push(withMarkerFix(createMarker(lineNumber, startColumn, endColumn, canonicalLocale ? `Unsupported locale. Use ${canonicalLocale} instead of ${localeEntry.text}.` : `Unsupported locale. ${localeEntry.text} is not a supported locale such as en-US or km-KH.`), canonicalLocale));
			return;
		}
		if (seenLocaleTags.has(localeEntry.text)) {
			markers.push(createMarker(lineNumber, startColumn, endColumn, `Duplicate locale. ${localeEntry.text} is already listed.`));
			return;
		}
		seenLocaleTags.add(localeEntry.text);
	});
}
function validateConfigBlock(bodyLines, startLineNumber, markers, declaredParts, allowZwspSeparators = true) {
	const multilineFieldNames = new Set(CONFIG_MULTILINE_FIELD_NAMES);
	const seenFieldLines = /* @__PURE__ */ new Map();
	let activeMultilineField = "";
	const takenFieldNames = /* @__PURE__ */ new Set();
	for (const line of bodyLines) {
		const entry = isCommentLine$1(line, allowZwspSeparators) ? null : line.match(CONFIG_ENTRY_RE$3);
		if (entry) takenFieldNames.add(normalizeConfigFieldName(entry[1].trim()));
	}
	bodyLines.forEach((line, index) => {
		if (isCommentLine$1(line, allowZwspSeparators)) return;
		const lineNumber = startLineNumber + index;
		const trimmedLine = trimSpaceLikeText(line, allowZwspSeparators);
		if (!trimmedLine) return;
		const configEntryMatch = line.match(CONFIG_ENTRY_RE$3);
		if (configEntryMatch) {
			const rawFieldName = configEntryMatch[1].trim();
			const fieldName = normalizeConfigFieldName(rawFieldName);
			const valueText = trimSpaceLikeText(configEntryMatch[2], allowZwspSeparators);
			const separatorOffset = line.indexOf(":");
			const valueOffset = separatorOffset === -1 ? line.length : separatorOffset + 1;
			const valueColumn = valueOffset + getLeadingSpaceLikeLength(line.slice(valueOffset), allowZwspSeparators) + 1;
			const existingLineNumber = seenFieldLines.get(fieldName);
			if (existingLineNumber) {
				const fieldStartColumn = line.indexOf(rawFieldName) + 1;
				markers.push(createMarker(lineNumber, fieldStartColumn, fieldStartColumn + rawFieldName.length, `Duplicate config field. ${fieldName} is already declared on line ${existingLineNumber}.`));
				activeMultilineField = multilineFieldNames.has(fieldName) ? fieldName : "";
				return;
			}
			seenFieldLines.set(fieldName, lineNumber);
			if (!valueText && !multilineFieldNames.has(fieldName)) {
				const colonColumn = line.indexOf(":") + 1;
				markers.push(createMarker(lineNumber, colonColumn, Math.max(colonColumn + 1, line.length + 1), `${fieldName} must provide a value on the same line.`));
			}
			if (fieldName === "Attachments" && valueText && !ATTACHMENT_VALUE_RE$1.test(valueText)) {
				const colonColumn = line.indexOf(":") + 1;
				markers.push(createMarker(lineNumber, colonColumn, Math.max(colonColumn + 1, line.length + 1), "Attachments must use a protocol-based URL such as http://, https://, file:///, ftp://, ftps://, or a Markdown link whose target is such a URL. Spaces inside the URL are allowed."));
			}
			if (fieldName === "Strumming Patterns" && valueText && !isValidStrummingPatternValue(valueText, allowZwspSeparators)) {
				const colonColumn = line.indexOf(":") + 1;
				markers.push(createMarker(lineNumber, colonColumn, Math.max(colonColumn + 1, line.length + 1), STRUMMING_PATTERN_MESSAGE));
			}
			const allowedValues = CONFIG_ENUM_FIELD_VALUES[fieldName];
			if (allowedValues && valueText && !allowedValues.includes(valueText)) {
				const colonColumn = line.indexOf(":") + 1;
				markers.push(withConfigValueFix(createMarker(lineNumber, colonColumn, Math.max(colonColumn + 1, line.length + 1), `${fieldName} must be one of: ${allowedValues.join(", ")}.`), suggestConfigFieldValue(fieldName, valueText)));
			}
			const valuePattern = CONFIG_PATTERN_FIELD_VALUES[fieldName];
			if (valuePattern && valueText && !valuePattern.test(valueText)) {
				const colonColumn = line.indexOf(":") + 1;
				markers.push(withConfigValueFix(createMarker(lineNumber, colonColumn, Math.max(colonColumn + 1, line.length + 1), CONFIG_PATTERN_FIELD_MESSAGES[fieldName] || `${fieldName} has an invalid value.`), suggestConfigFieldValue(fieldName, valueText)));
			}
			if (fieldName === "Locales" && valueText) validateLocalesValue(valueText, lineNumber, valueColumn, markers, allowZwspSeparators);
			if (fieldName === "Structure" && valueText) validateStructureValue(valueText, lineNumber, valueColumn, markers, declaredParts);
			activeMultilineField = multilineFieldNames.has(fieldName) ? fieldName : "";
			return;
		}
		const malformedFieldMatch = /^[ \t]+/.test(line) ? null : line.match(CONFIG_FIELD_LINE_RE$3);
		if (malformedFieldMatch) {
			const rawFieldName = malformedFieldMatch[1].trim();
			const fieldName = normalizeConfigFieldName(rawFieldName);
			const dashIndex = line.indexOf("-");
			const nameIndex = rawFieldName ? line.indexOf(rawFieldName, dashIndex + 1) : -1;
			const fieldStartColumn = nameIndex === -1 ? dashIndex + 3 : nameIndex + 1;
			const fieldEndColumn = fieldStartColumn + Math.max(1, rawFieldName.length);
			if (rawFieldName && !CONFIG_FIELD_NAMES.includes(fieldName)) {
				const suggestion = suggestConfigFieldName(rawFieldName, takenFieldNames);
				if (suggestion) takenFieldNames.add(suggestion);
				markers.push(withMarkerFix(createMarker(lineNumber, fieldStartColumn, fieldEndColumn, suggestion ? `Unsupported config field. Did you mean ${suggestion}?` : UNSUPPORTED_CONFIG_FIELD_MESSAGE), suggestion));
			} else markers.push(createMarker(lineNumber, 1, Math.max(4, line.length + 1), "Invalid config entry. Use - Field: value."));
			activeMultilineField = "";
			return;
		}
		if (!activeMultilineField) {
			const startColumn = getNonWhitespaceColumn(line, allowZwspSeparators);
			markers.push(createMarker(lineNumber, startColumn, Math.max(startColumn + 1, line.length + 1), "Config continuation lines must follow a Description, Attachments, or Strumming Patterns entry."));
		} else if (activeMultilineField === "Attachments" && (!/^[ \t]+/.test(line) || !ATTACHMENT_VALUE_RE$1.test(trimmedLine))) {
			const startColumn = getNonWhitespaceColumn(line, allowZwspSeparators);
			markers.push(createMarker(lineNumber, startColumn, Math.max(startColumn + 1, line.length + 1), "Attachments continuation lines must start with spaces or tabs and contain a protocol-based URL such as http://, https://, file:///, ftp://, ftps://, or a Markdown link that points to one. Spaces inside the URL are allowed."));
		} else if (activeMultilineField === "Strumming Patterns" && (!/^[ \t]+/.test(line) || !isValidStrummingPatternValue(trimmedLine, allowZwspSeparators))) {
			const startColumn = getNonWhitespaceColumn(line, allowZwspSeparators);
			markers.push(createMarker(lineNumber, startColumn, Math.max(startColumn + 1, line.length + 1), STRUMMING_PATTERN_CONTINUATION_MESSAGE));
		}
	});
	const missingRequiredFields = CONFIG_REQUIRED_FIELD_NAMES.filter((fieldName) => !seenFieldLines.has(fieldName));
	if (missingRequiredFields.length) {
		const headerLineNumber = Math.max(1, startLineNumber - 1);
		markers.push(createMarker(headerLineNumber, 1, 12, `Missing required config fields: ${missingRequiredFields.join(", ")}.`));
	}
}
/**
* Does a parenthesised token look like a botched repeat suffix?
*
* `REPEAT_SUFFIX_RE` only accepts the exact `(2x)` spelling, so every other
* parenthesised token reaches this check. `(2 x)`, `(0x)` and `(2X)` are
* clearly repeats that got the format wrong and earn the "use exact format"
* hint; `(hello)` is not a repeat at all and stays a plain invalid token.
*/
function isRepeatLikeText(text) {
	return /^\s*\d+\s*[xX]\s*$/.test(text);
}
/**
* `(2x)` for a repeat suffix written `( 2 X )`; `''` when the count itself is
* wrong (`(0x)`), as no spelling of it is valid.
*/
function formatRepeatSuffix(text) {
	const suffix = `(${String(text).match(/\d+/)?.[0] ?? ""}x)`;
	return REPEAT_SUFFIX_RE$1.test(suffix) ? suffix : "";
}
function validateProgressionTokens(joined, startOffset, markers, sectionLabel, allowZwspSeparators = true) {
	const text = joined.text;
	let offset = startOffset;
	while (offset < text.length) {
		offset = skipSpaces(text, offset, allowZwspSeparators);
		if (offset >= text.length) return;
		const remaining = text.slice(offset);
		const repeatMatch = remaining.match(REPEAT_SUFFIX_RE$1);
		if (repeatMatch) {
			offset += repeatMatch[0].length;
			continue;
		}
		if (text[offset] === "(") {
			const closingIndex = text.indexOf(")", offset + 1);
			if (closingIndex === -1) {
				pushJoinedMarker(markers, joined, offset, text.length, "Unclosed repeat suffix.");
				return;
			}
			const suffixText = text.slice(offset + 1, closingIndex);
			const token = text.slice(offset, closingIndex + 1);
			const isRepeat = isRepeatLikeText(suffixText);
			const message = isRepeat ? "Repeat suffix must use exact format (2x)." : getProgressionTokenMessage(token, sectionLabel);
			withMarkerFix(pushJoinedMarker(markers, joined, offset, closingIndex + 1, message), isRepeat ? formatRepeatSuffix(suffixText) : suggestProgressionChord(token));
			return;
		}
		const barMatch = remaining.match(/^(?:\|\|:|\|:|:\|\||:\||\|)/);
		if (barMatch) {
			offset += barMatch[0].length;
			continue;
		}
		const chordMatch = remaining.match(CHORD_SYMBOL_RE);
		if (chordMatch) {
			offset += chordMatch[0].length;
			continue;
		}
		const endOffset = findTokenBoundary(text, offset, allowZwspSeparators);
		const token = text.slice(offset, endOffset);
		withMarkerFix(pushJoinedMarker(markers, joined, offset, endOffset, getProgressionTokenMessage(token, sectionLabel)), suggestProgressionChord(token));
		offset = endOffset;
	}
}
function validateDirectiveBlock(bodyLines, startLineNumber, markers, sectionLabel, directivePattern, directiveExample, allowZwspSeparators = true) {
	const joined = buildJoinedText(bodyLines, startLineNumber, allowZwspSeparators);
	if (!joined.text) return;
	const text = joined.text;
	let offset = skipSpaces(text, 0, allowZwspSeparators);
	if (offset < text.length && text[offset] === "{") {
		const directiveMatch = text.slice(offset).match(directivePattern);
		if (!directiveMatch) {
			pushJoinedMarker(markers, joined, offset, findClosingBrace(text, offset), `Invalid ${sectionLabel.toLowerCase()} directive. Expected ${directiveExample}.`);
			return;
		}
		offset += directiveMatch[0].length;
	}
	offset = skipSpaces(text, offset, allowZwspSeparators);
	if (offset >= text.length) return;
	validateProgressionTokens(joined, offset, markers, sectionLabel, allowZwspSeparators);
}
function validateLyricBlock(bodyLines, startLineNumber, markers, allowZwspSeparators = true) {
	bodyLines.forEach((line, index) => {
		if (isCommentLine$1(line, allowZwspSeparators)) return;
		if (!trimSpaceLikeText(line, allowZwspSeparators)) return;
		const lineNumber = startLineNumber + index;
		let offset = 0;
		while (offset < line.length) {
			const currentChar = line[offset];
			if (currentChar === "|") {
				offset += 1;
				continue;
			}
			if (currentChar === "[") {
				const closingIndex = line.indexOf("]", offset + 1);
				if (closingIndex === -1) {
					markers.push(createMarker(lineNumber, offset + 1, line.length + 1, "Unclosed chord annotation."));
					return;
				}
				const annotation = line.slice(offset, closingIndex + 1);
				if (!CHORD_ANNOTATION_RE.test(annotation)) markers.push(withMarkerFix(createMarker(lineNumber, offset + 1, closingIndex + 2, getChordAnnotationMessage(annotation, allowZwspSeparators)), suggestChordAnnotation(annotation, allowZwspSeparators)));
				offset = closingIndex + 1;
				continue;
			}
			if (currentChar === "]") markers.push(createMarker(lineNumber, offset + 1, offset + 2, "Unexpected closing bracket in lyric line."));
			offset += 1;
		}
	});
}
/**
* Does this line read as chord notation rather than lyric text?
*
* The test is a deliberate syntactic tell — a bar or a `{p:}`/`{c:}` cue —
* not "do all the tokens happen to be chords". Only a marker can separate an
* intended progression from a lyric, and only a line claiming to be a
* progression may be held to progression syntax: without the marker a
* mistyped chord would demote itself to lyric text and the error would
* vanish. It is the same rule OnSong uses to spot a chord line.
*/
function isMixedProgressionLine(line, allowZwspSeparators = true) {
	const trimmedLine = trimSpaceLikeText(line, allowZwspSeparators);
	return Boolean(trimmedLine) && (hasChordProgressionText(trimmedLine, allowZwspSeparators) || /^\{[cp]:/.test(trimmedLine));
}
function validateMixedProgressionLine(line, lineNumber, markers, sectionLabel, allowZwspSeparators = true) {
	const joined = buildJoinedText([line], lineNumber, allowZwspSeparators);
	if (!joined.text) return;
	const text = joined.text;
	let offset = skipSpaces(text, 0, allowZwspSeparators);
	if (offset < text.length && text[offset] === "{") {
		const remaining = text.slice(offset);
		const directiveMatch = remaining.match(INTRO_DIRECTIVE_RE) || remaining.match(INSTRUMENTAL_DIRECTIVE_RE);
		if (!directiveMatch) {
			pushJoinedMarker(markers, joined, offset, findClosingBrace(text, offset), `Invalid ${sectionLabel.toLowerCase()} directive. Expected {p: #3} or {c: Piano + Pads }.`);
			return;
		}
		offset += directiveMatch[0].length;
	}
	offset = skipSpaces(text, offset, allowZwspSeparators);
	if (offset >= text.length) return;
	validateProgressionTokens(joined, offset, markers, sectionLabel, allowZwspSeparators);
}
/**
* Validate a section that may hold either chord progressions or lyrics —
* `Intro` and `Outro`.
*
* Unlike `validateDirectiveBlock`, which joins the whole body into one
* progression, this classifies **each line** on its own, so a sung intro can
* sit under the progression that sets it up.
*/
function validateMixedBlock(bodyLines, startLineNumber, markers, sectionLabel, allowZwspSeparators = true) {
	bodyLines.forEach((line, index) => {
		if (isCommentLine$1(line, allowZwspSeparators) || !trimSpaceLikeText(line, allowZwspSeparators)) return;
		const lineNumber = startLineNumber + index;
		if (isMixedProgressionLine(line, allowZwspSeparators)) {
			validateMixedProgressionLine(line, lineNumber, markers, sectionLabel, allowZwspSeparators);
			return;
		}
		validateLyricBlock([line], lineNumber, markers, allowZwspSeparators);
	});
}
function validateFenceBody(header, bodyLines, startLineNumber, markers, declaredParts, allowZwspSeparators = true) {
	header.definition.validateBody({
		header,
		bodyLines,
		startLineNumber,
		markers,
		declaredParts,
		validators: {
			validateConfigBlock: (...args) => validateConfigBlock(...args, allowZwspSeparators),
			validateDirectiveBlock: (...args) => validateDirectiveBlock(...args, allowZwspSeparators),
			validateLyricBlock: (...args) => validateLyricBlock(...args, allowZwspSeparators),
			validateMixedBlock: (...args) => validateMixedBlock(...args, allowZwspSeparators)
		},
		directivePatterns: {
			intro: INTRO_OR_CUE_DIRECTIVE_RE,
			instrumental: INSTRUMENTAL_DIRECTIVE_RE
		}
	});
}
function collectDeclaredParts(lines) {
	const declaredParts = /* @__PURE__ */ new Map();
	let lineIndex = 0;
	while (lineIndex < lines.length) {
		const headerMatch = lines[lineIndex].match(/^\s*```ol:(.*)$/);
		if (!headerMatch) {
			lineIndex += 1;
			continue;
		}
		const header = parseFenceHeader(headerMatch[1].trim());
		let closingIndex = lineIndex + 1;
		while (closingIndex < lines.length && !/^\s*```\s*$/.test(lines[closingIndex])) closingIndex += 1;
		if (header && (!declaredParts.has(header.partName) || header.definition.allowsDuplicateDeclaredPart())) declaredParts.set(header.partName, lineIndex + 1);
		if (closingIndex >= lines.length) break;
		lineIndex = closingIndex + 1;
	}
	return declaredParts;
}
function collectMarkdownOlMarkersFromLines(lines) {
	const markers = [];
	const allowZwspSeparators = shouldAllowInvisibleWordSeparators(lines.join("\n"));
	const declaredParts = collectDeclaredParts(lines);
	const seenParts = /* @__PURE__ */ new Map();
	let lineIndex = 0;
	while (lineIndex < lines.length) {
		const line = lines[lineIndex];
		const headerMatch = line.match(/^\s*```ol:(.*)$/);
		if (!headerMatch) {
			lineIndex += 1;
			continue;
		}
		const info = headerMatch[1].trim();
		const header = parseFenceHeader(info);
		let closingIndex = lineIndex + 1;
		while (closingIndex < lines.length && !/^\s*```\s*$/.test(lines[closingIndex])) closingIndex += 1;
		const hasClosingFence = closingIndex < lines.length;
		const bodyLines = lines.slice(lineIndex + 1, hasClosingFence ? closingIndex : lines.length);
		if (!header) {
			const infoOffset = Math.max(0, line.indexOf("ol:") + 3);
			const headerFix = getFenceHeaderFix(info);
			markers.push(withMarkerFix(createMarker(lineIndex + 1, infoOffset + 1, Math.max(infoOffset + 2, line.length + 1), getFenceHeaderError(info)), headerFix, `Change to ol:${headerFix}`));
		} else {
			const existingLineNumber = seenParts.get(header.partName);
			if (existingLineNumber && !header.definition.allowsDuplicateDeclaredPart()) {
				const infoOffset = Math.max(0, line.indexOf("ol:") + 3);
				markers.push(createMarker(lineIndex + 1, infoOffset + 1, Math.max(infoOffset + header.partName.length + 1, line.length + 1), `Duplicate ol part. ${header.partName} is already declared on line ${existingLineNumber}.`));
			} else seenParts.set(header.partName, lineIndex + 1);
			validateFenceBody(header, bodyLines, lineIndex + 2, markers, declaredParts, allowZwspSeparators);
		}
		if (!hasClosingFence) {
			markers.push(createMarker(lineIndex + 1, 1, Math.max(4, line.length + 1), "Unclosed ol fence."));
			break;
		}
		lineIndex = closingIndex + 1;
	}
	getRequiredDeclaredPartNames().forEach((partName) => {
		if (!declaredParts.has(partName)) markers.push(createDocumentMarker(lines, `Missing required ol part. Add ol:${partName}.`, getErrorMarkerSeverity(), allowZwspSeparators));
	});
	return markers;
}
function splitMarkdownOlText(text) {
	return String(text).replace(/\r\n?/g, "\n").split("\n");
}
//#endregion
//#region src/plugins/OpenLyric/domain/fence-locations.ts
/**
* Where the fences of a document sit in its source, and how the previews key
* them.
*
* Deliberately dependency-light — the parser registry and nothing else — so a
* surface that renders no preview (a bare `Editor`, the editor-only page) can
* ask "which line is `Chorus 1` on?" without pulling the markdown render
* pipeline (`marked`, the preview helpers) into its bundle. The preview layer
* imports the same functions rather than keeping its own copies, so a fence id
* computed here is exactly the id the preview rendered.
*/
/** One complete ```` ```ol:… ```` block: header info and body captured. */
var OL_FENCE_BLOCK_RE$1 = /^```ol:([^\r\n]*)[ \t]*\r?\n([\s\S]*?)^```[ \t]*$/gm;
var PREVIEW_TARGET_ID_PREFIX = "ol-preview-target-";
var SONG_VIEW_TARGET_ID_PREFIX = "ol-song-view-target-";
function normalizeNewlines$5(value) {
	return String(value ?? "").replace(/\r\n?/g, "\n");
}
function createPreviewTargetId(value) {
	const slug = String(value ?? "").trim().toLowerCase().replace(/[^a-z0-9]+/g, "-").replace(/^-+|-+$/g, "");
	return slug ? `${PREVIEW_TARGET_ID_PREFIX}${slug}` : "";
}
function createSongViewTargetId(partName) {
	const previewTargetId = createPreviewTargetId(partName);
	return previewTargetId ? previewTargetId.replace(PREVIEW_TARGET_ID_PREFIX, SONG_VIEW_TARGET_ID_PREFIX) : "";
}
function getLineNumberAtOffset$2(text, offset) {
	if (offset <= 0) return 1;
	return text.slice(0, offset).split("\n").length;
}
function getLineNumberAtEndOffset$1(text, endOffset) {
	if (endOffset <= 0) return 1;
	return getLineNumberAtOffset$2(text, Math.max(0, endOffset - 1));
}
function parseOpenLyricFences(markdown) {
	const normalizedMarkdown = normalizeNewlines$5(markdown);
	return Array.from(normalizedMarkdown.matchAll(OL_FENCE_BLOCK_RE$1)).map((match) => {
		const info = String(match[1] ?? "").trim();
		const parsedHeader = parseFenceHeader(info);
		if (!parsedHeader?.definition) return null;
		return {
			info,
			raw: match[0] || "",
			body: match[2] || "",
			parsedHeader,
			startLineNumber: getLineNumberAtOffset$2(normalizedMarkdown, match.index || 0),
			endLineNumber: getLineNumberAtEndOffset$1(normalizedMarkdown, (match.index || 0) + String(match[0] || "").length)
		};
	}).filter((fence) => Boolean(fence));
}
/**
* Every recognized fence the document declares, in source order.
*
* Only fences whose header the registry knows are listed — the same rule the
* previews render by, so `id`/`songViewId` always name an element the
* corresponding preview actually emitted (an unrecognized ```` ```ol:… ````
* block renders as an "unknown" fence and is skipped here too).
*/
function listOpenLyricFences(markdown) {
	return parseOpenLyricFences(markdown).map((fence) => {
		const partName = String(fence.parsedHeader?.partName ?? "");
		return {
			id: createPreviewTargetId(partName),
			songViewId: createSongViewTargetId(partName),
			partName,
			kind: String(fence.parsedHeader?.kind ?? ""),
			header: String(fence.parsedHeader?.header ?? ""),
			startLine: fence.startLineNumber,
			endLine: fence.endLineNumber
		};
	});
}
//#endregion
//#region src/plugins/OpenLyric/document/song-object.ts
var LIST_FIELD_NAMES = /* @__PURE__ */ new Set(["Description", "Attachments"]);
var STRUMMING_PATTERNS_FIELD = "Strumming Patterns";
/**
* Fields written as one comma-separated line and carried as a list. Both use
* the `Locales` separator, a plain comma.
*/
var COMMA_LIST_FIELD_NAMES = /* @__PURE__ */ new Set(["Locales", "Keywords"]);
var CONFIG_HEADER = "Config";
var COMMENT_LINE_RE$1 = /^\s*\/\//;
var COMMENT_PREFIX_RE = /^\s*\/\/\s?/;
var CONFIG_ENTRY_RE$2 = new RegExp(`^\\s*-\\s*(${CONFIG_FIELD_MATCH_NAMES$1.map(escapeRegex).join("|")})\\s*:(.*)$`);
var CONFIG_FIELD_LINE_RE$2 = /^\s*-\s*([^:]+?)\s*:(.*)$/;
function normalizeNewlines$4(value) {
	return String(value ?? "").replace(/\r\n?/g, "\n");
}
function splitFenceBody(body) {
	const lines = normalizeNewlines$4(body).split("\n");
	if (lines.length && lines[lines.length - 1] === "") lines.pop();
	return lines;
}
function collectConfigEntries(bodyLines, warnings) {
	const entries = [];
	let current = null;
	bodyLines.forEach((line) => {
		if (!line.trim()) return;
		if (COMMENT_LINE_RE$1.test(line)) {
			if (current) current.rest.push({
				text: line.replace(COMMENT_PREFIX_RE, "").trim(),
				isComment: true
			});
			else warnings.push(`Config comment "${line.trim()}" precedes every field and has no place in a song object.`);
			return;
		}
		const entryMatch = line.match(CONFIG_ENTRY_RE$2);
		if (entryMatch) {
			current = {
				name: normalizeConfigFieldName(entryMatch[1]),
				first: String(entryMatch[2] ?? "").trim(),
				rest: []
			};
			entries.push(current);
			return;
		}
		const unknownFieldMatch = /^[ \t]/.test(line) ? null : line.match(CONFIG_FIELD_LINE_RE$2);
		if (unknownFieldMatch) {
			warnings.push(`Unsupported Config field "${unknownFieldMatch[1].trim()}" was left out.`);
			current = null;
			return;
		}
		if (current) current.rest.push({
			text: line.trim(),
			isComment: false
		});
		else warnings.push(`Config line "${line.trim()}" belongs to no field and was left out.`);
	});
	return entries;
}
function readListValue(entry, warnings) {
	const values = entry.first ? [entry.first] : [];
	entry.rest.forEach(({ text, isComment }) => {
		if (isComment) {
			warnings.push(`Comment "// ${text}" inside ${entry.name} has no place in a song object and was left out.`);
			return;
		}
		values.push(text);
	});
	return values;
}
function readStrummingPatterns(entry) {
	const patterns = [];
	let pendingLabel;
	if (entry.first) patterns.push({ pattern: entry.first });
	entry.rest.forEach(({ text, isComment }) => {
		if (isComment) {
			pendingLabel = text;
			return;
		}
		patterns.push(pendingLabel ? {
			label: pendingLabel,
			pattern: text
		} : { pattern: text });
		pendingLabel = void 0;
	});
	return patterns;
}
function readScalarValue(entry, warnings) {
	const values = [entry.first];
	entry.rest.forEach(({ text, isComment }) => {
		if (isComment) {
			warnings.push(`Comment "// ${text}" after ${entry.name} has no place in a song object and was left out.`);
			return;
		}
		values.push(text);
	});
	return values.filter(Boolean).join(" ");
}
function readConfig(bodyLines, warnings) {
	const config = {
		Title: "",
		Structure: ""
	};
	const seen = /* @__PURE__ */ new Set();
	collectConfigEntries(bodyLines, warnings).forEach((entry) => {
		if (seen.has(entry.name)) {
			warnings.push(`Duplicate Config field "${entry.name}" — only the first is kept.`);
			return;
		}
		seen.add(entry.name);
		if (entry.name === STRUMMING_PATTERNS_FIELD) {
			config[entry.name] = readStrummingPatterns(entry);
			return;
		}
		if (LIST_FIELD_NAMES.has(entry.name)) {
			config[entry.name] = readListValue(entry, warnings);
			return;
		}
		if (COMMA_LIST_FIELD_NAMES.has(entry.name)) {
			config[entry.name] = readScalarValue(entry, warnings).split(",").map((tag) => tag.trim()).filter(Boolean);
			return;
		}
		config[entry.name] = readScalarValue(entry, warnings);
	});
	return config;
}
function collectPreamble(markdown, fenceRanges) {
	return markdown.split("\n").filter((_line, index) => {
		const lineNumber = index + 1;
		return !fenceRanges.some((range) => lineNumber >= range.startLineNumber && lineNumber <= range.endLineNumber);
	}).join("\n").replace(/\n{3,}/g, "\n\n").trim();
}
/**
* Read a song object out of an Open Lyric document. Fences with an
* unrecognized header are not sections and stay out of the object (and out of
* the preamble); the validator reports them.
*/
function songObjectFromMarkdown(markdown) {
	const text = normalizeNewlines$4(markdown);
	const warnings = [];
	const fences = parseOpenLyricFences(text);
	const configFences = fences.filter((fence) => fence.parsedHeader?.header === CONFIG_HEADER);
	if (!configFences.length) warnings.push("The document has no ol:Config fence.");
	else if (configFences.length > 1) warnings.push(`The document has ${configFences.length} ol:Config fences — only the first is read.`);
	return {
		song: {
			config: configFences.length ? readConfig(splitFenceBody(configFences[0].body), warnings) : {
				Title: "",
				Structure: ""
			},
			sections: fences.filter((fence) => fence.parsedHeader?.header !== CONFIG_HEADER).map((fence) => {
				const indexText = String(fence.parsedHeader?.indexText ?? "").trim();
				const section = {
					header: String(fence.parsedHeader?.header ?? ""),
					lines: splitFenceBody(fence.body)
				};
				if (indexText) section.index = Number(indexText);
				return section;
			})
		},
		preamble: collectPreamble(text, fences),
		warnings
	};
}
function toStringList(value) {
	if (Array.isArray(value)) return value.map((item) => String(item ?? "").trim()).filter(Boolean);
	const single = String(value ?? "").trim();
	return single ? [single] : [];
}
function toStrummingPatterns(value) {
	return (Array.isArray(value) ? value : value == null ? [] : [value]).map((item) => {
		if (item && typeof item === "object") {
			const record = item;
			const pattern = String(record.pattern ?? "").trim();
			const label = String(record.label ?? "").trim();
			return label ? {
				label,
				pattern
			} : { pattern };
		}
		return { pattern: String(item ?? "").trim() };
	}).filter((item) => item.pattern);
}
/**
* The notation lines one Config field is written as — `- Name: value`, plus
* indented continuation lines for the multiline fields (`Description`,
* `Attachments`, `Strumming Patterns`, whose labels are `//` lines above their
* pattern). An empty value writes nothing. `name` must be canonical (aliases
* already resolved).
*/
function formatConfigFieldLines(name, value, indent = "	") {
	const lines = [];
	writeConfigField(lines, name, value, indent);
	return lines;
}
function writeConfigField(lines, name, value, indent) {
	if (value == null) return;
	if (name === STRUMMING_PATTERNS_FIELD) {
		const patterns = toStrummingPatterns(value);
		if (!patterns.length) return;
		if (patterns[0].label) {
			lines.push(`- ${name}:`);
			patterns.forEach(({ label, pattern }) => {
				if (label) lines.push(`${indent}// ${label}`);
				lines.push(`${indent}${pattern}`);
			});
			return;
		}
		lines.push(`- ${name}: ${patterns[0].pattern}`);
		patterns.slice(1).forEach(({ label, pattern }) => {
			if (label) lines.push(`${indent}// ${label}`);
			lines.push(`${indent}${pattern}`);
		});
		return;
	}
	if (LIST_FIELD_NAMES.has(name)) {
		const values = toStringList(value);
		if (!values.length) return;
		lines.push(`- ${name}: ${values[0]}`);
		values.slice(1).forEach((line) => lines.push(`${indent}${line}`));
		return;
	}
	if (COMMA_LIST_FIELD_NAMES.has(name)) {
		const tags = toStringList(value).flatMap((tag) => tag.split(",").map((part) => part.trim()).filter(Boolean));
		if (tags.length) lines.push(`- ${name}: ${tags.join(`, `)}`);
		return;
	}
	const text = String(value).replace(/\s*\r?\n\s*/g, " ").trim();
	if (text) lines.push(`- ${name}: ${text}`);
}
/**
* Write a song object as an Open Lyric document: the optional preamble, the
* `ol:Config` fence with its fields in canonical order, then every section in
* the object's order. Fields outside the schema are ignored. The result is
* not validated here.
*/
function songObjectToMarkdown(song, { preamble = "", indent = "	" } = {}) {
	const config = song?.config ?? {};
	const lines = [];
	const trimmedPreamble = normalizeNewlines$4(preamble).trim();
	if (trimmedPreamble) lines.push(trimmedPreamble, "");
	lines.push("```ol:Config");
	CONFIG_FIELD_NAMES$1.forEach((name) => {
		writeConfigField(lines, name, config[name], indent);
	});
	lines.push("```");
	(Array.isArray(song?.sections) ? song.sections : []).forEach((section) => {
		const header = String(section?.header ?? "").trim();
		const indexText = section?.index == null || section.index === "" ? "" : String(section.index).trim();
		const bodyLines = Array.isArray(section?.lines) ? section.lines.map((line) => normalizeNewlines$4(line).split("\n")).flat() : [];
		lines.push("", `\`\`\`ol:${formatDeclaredPartName(header, indexText)}`, ...bodyLines, "```");
	});
	return `${lines.join("\n")}\n`;
}
//#endregion
//#region src/plugins/OpenLyric/preview/controller/section-chords.ts
var CHORD_INSERT_STYLES = /* @__PURE__ */ new Set([
	"annotation",
	"progression",
	"mixed"
]);
var SONG_CHORD_LIMIT = 16;
var BARE_CHORD_RE$3 = new RegExp(`^${CHORD_SYMBOL_SOURCE}$`);
var CHORD_ANNOTATION_GLOBAL_RE = new RegExp(String.raw`\[(${CHORD_SYMBOL_SOURCE})\]`, "g");
var PROGRESSION_SEPARATOR_RE = /(\{[^{}\r\n]+\}|\|\|:|\|:|:\|\||:\||\||\([1-9]\d*x\))/g;
function normalizeChordInsertStyle(value) {
	const style = String(value ?? "").trim();
	return CHORD_INSERT_STYLES.has(style) ? style : "annotation";
}
function isValidChordSymbol(value) {
	return BARE_CHORD_RE$3.test(String(value ?? ""));
}
/** Does this line read as a chord progression rather than a sung line? */
function isProgressionLine(line) {
	const trimmedLine = String(line ?? "").trim();
	return Boolean(trimmedLine) && (hasChordProgressionText(trimmedLine) || /^\{[cp]:/.test(trimmedLine));
}
function listBareChordTokens(line) {
	return String(line ?? "").replace(PROGRESSION_SEPARATOR_RE, " ").split(/[\s\u200B]+/u).filter((token) => isValidChordSymbol(token));
}
function collectLineChords(line, style, into) {
	for (const match of String(line ?? "").matchAll(CHORD_ANNOTATION_GLOBAL_RE)) into.push(match[1]);
	if (style === "progression" || isProgressionLine(line)) into.push(...listBareChordTokens(line));
}
/**
* Every chord the song already uses, in first-appearance order, deduplicated.
*
* `draftText` is the open section editor's textarea — not saved yet, but a
* chord the reader has just inserted there is one they will want again on the
* next line.
*/
function collectSongChords(markdown, draftText = "", limit = SONG_CHORD_LIMIT) {
	const chords = [];
	for (const fence of parseOpenLyricFences(markdown)) {
		if (fence.parsedHeader?.header === "Config") continue;
		const style = normalizeChordInsertStyle(fence.parsedHeader?.definition?.getPreviewChordInsertStyle?.());
		for (const line of String(fence.body ?? "").split("\n")) collectLineChords(line, style, chords);
	}
	for (const line of String(draftText ?? "").split("\n")) collectLineChords(line, "annotation", chords);
	return Array.from(new Set(chords)).slice(0, Math.max(0, limit));
}
//#endregion
//#region src/open-lyric-mcp/operations/analysis.ts
var SEVERITY_NAMES = {
	8: "error",
	4: "warning",
	2: "information",
	1: "hint"
};
function validateSong(text) {
	const diagnostics = collectMarkdownOlMarkersFromLines(splitMarkdownOlText(String(text ?? ""))).map((marker) => ({
		message: String(marker.message),
		severity: SEVERITY_NAMES[Number(marker.severity)] ?? "error",
		line: Number(marker.startLineNumber),
		column: Number(marker.startColumn),
		endLine: Number(marker.endLineNumber),
		endColumn: Number(marker.endColumn),
		...marker.fix ? { fix: {
			title: String(marker.fix.title),
			text: String(marker.fix.text)
		} } : {}
	})).sort((a, b) => a.line - b.line || a.column - b.column);
	const errorCount = diagnostics.filter((diagnostic) => diagnostic.severity === "error").length;
	return {
		valid: errorCount === 0,
		errorCount,
		warningCount: diagnostics.filter((diagnostic) => diagnostic.severity === "warning").length,
		diagnostics
	};
}
/** A one-paragraph, human-readable account of a validation result. */
function summarizeValidation(validation) {
	if (!validation.diagnostics.length) return "Valid Open Lyric: no diagnostics.";
	const lines = validation.diagnostics.slice(0, 20).map((diagnostic) => `- line ${diagnostic.line}:${diagnostic.column} ${diagnostic.severity}: ${diagnostic.message}`);
	if (validation.diagnostics.length > 20) lines.push(`- … and ${validation.diagnostics.length - 20} more`);
	return [`${validation.errorCount} error(s), ${validation.warningCount} warning(s):`, ...lines].join("\n");
}
function getRepeatCount(repeatText) {
	const match = String(repeatText ?? "").match(/^(\d+)x$/);
	return match ? Number.parseInt(match[1], 10) : 1;
}
/**
* Read a `Structure` value — the compact performance order — step by step.
* With `declaredPartNames`, each step says whether a fence declares its part
* and the result lists what is missing and what is unused.
*/
function describeStructure(structure, declaredPartNames) {
	const parsed = parseStructureValue(String(structure ?? "").trim());
	const declared = declaredPartNames ? new Set(declaredPartNames) : null;
	const steps = (parsed.steps || []).map((step) => {
		const partName = String(step.partName || step.partText || "");
		const info = {
			code: `${step.code ?? ""}${step.indexText ?? ""}`,
			partName,
			repeat: getRepeatCount(step.repeatText),
			label: formatStructureStepLabel(step)
		};
		if (declared) info.declared = declared.has(partName);
		return info;
	});
	const playedParts = new Set(steps.map((step) => step.partName));
	return {
		text: String(parsed.text ?? structure ?? ""),
		error: parsed.error?.message ?? null,
		steps,
		undeclaredParts: declared ? Array.from(new Set(steps.filter((step) => !declared.has(step.partName)).map((step) => step.partName))) : [],
		unusedSections: declared ? Array.from(declared).filter((partName) => !playedParts.has(partName)) : []
	};
}
function listSongSections(text) {
	const { song } = songObjectFromMarkdown(text);
	const playedParts = new Set(describeStructure(song.config.Structure).steps.map((step) => step.partName));
	return listOpenLyricFences(text).filter((fence) => fence.header !== "Config").map((fence) => {
		const indexMatch = fence.partName.match(/\s([1-9]\d*)$/);
		const info = {
			partName: fence.partName,
			header: fence.header,
			kind: fence.kind,
			startLine: fence.startLine,
			endLine: fence.endLine,
			lineCount: Math.max(0, fence.endLine - fence.startLine - 1),
			inStructure: playedParts.has(fence.partName)
		};
		if (indexMatch) info.index = Number(indexMatch[1]);
		return info;
	});
}
var SONG_CHORD_SCAN_LIMIT = 1e3;
function listSongChords(text) {
	const { song } = songObjectFromMarkdown(text);
	const key = parseMainKey(song.config.Key ?? "")?.raw ?? "";
	const diatonicTriads = key ? getKeyDiatonicTriads(key) : [];
	return {
		key,
		diatonicTriads,
		chords: collectSongChords(text, "", SONG_CHORD_SCAN_LIMIT).map((chord) => {
			const simplified = simplifyChordSymbol(chord);
			const info = {
				chord,
				name: describeChordKey(chord).replace(/^Chord\s+/, ""),
				simplified,
				degreeHints: createChordDegreeHints(chord)
			};
			if (key) info.inKey = diatonicTriads.includes(chord) || diatonicTriads.includes(simplified);
			return info;
		})
	};
}
function getSongInfo(text) {
	const { song, warnings } = songObjectFromMarkdown(text);
	const config = song.config;
	const sections = listSongSections(text);
	const info = {
		hasConfig: listOpenLyricFences(text).some((fence) => fence.header === "Config"),
		title: config.Title || "",
		description: config.Description ?? [],
		locales: config.Locales ?? [],
		keywords: config.Keywords ?? [],
		structure: describeStructure(config.Structure, sections.map((section) => section.partName)),
		sections,
		chords: collectSongChords(text, "", SONG_CHORD_SCAN_LIMIT),
		attachments: createOpenLyricAttachments(config.Attachments ?? []).map((attachment) => ({
			title: String(attachment.title ?? ""),
			type: String(attachment.type ?? ""),
			link: String(attachment.link ?? "")
		})),
		strummingPatterns: config["Strumming Patterns"] ?? [],
		warnings
	};
	const optionalFields = {
		subtitle: config.Subtitle,
		artist: config.Artist,
		copyright: config.Copyright,
		key: config.Key,
		tempo: config.Tempo,
		time: config.Time,
		theme: config.Theme,
		genre: config.Genre,
		style: config.Style,
		year: config.Year,
		melody: config.Melody
	};
	Object.entries(optionalFields).forEach(([field, value]) => {
		if (value) info[field] = value;
	});
	return info;
}
//#endregion
//#region src/editor/scripts/invisible-characters.ts
/**
* Every code point worth flagging: C0/C1 controls, the Unicode space and
* separator blocks, and the format (`Cf`) category — ZWSP, ZWNJ, ZWJ, BOM, the
* bidi controls, and friends.
*/
var INVISIBLE_CHARACTER_REGEX = /[\u0000-\u0008\u000B-\u001F\u007F-\u009F\u00A0\u1680\u180E\u2000-\u200F\u2028-\u202F\u205F-\u206F\u3000\u3164\uFFA0\uFEFF\p{Cf}]/gu;
/** Matches two or more adjacent invisible characters (what Format collapses). */
function createDuplicateInvisibleCharacterRunRegex() {
	return new RegExp(`(?:${INVISIBLE_CHARACTER_REGEX.source}){2,}`, INVISIBLE_CHARACTER_REGEX.flags);
}
var TRAILING_FORMATTABLE_WHITESPACE_RE = new RegExp(`(?:\\s|${INVISIBLE_CHARACTER_REGEX.source})+$`, INVISIBLE_CHARACTER_REGEX.flags.replace("g", ""));
/**
* One line as the editor's Format Document command leaves it: word separators
* normalized for the line's script, every run of repeated invisible
* characters collapsed to its first, and trailing whitespace (visible or not)
* removed. Pure, so a host with no editor — the MCP server's `format_song` —
* formats a song exactly the way the Monaco surface does.
*/
function formatDocumentLineWhitespace(lineContent) {
	return normalizeWordSeparators(String(lineContent ?? "")).replace(createDuplicateInvisibleCharacterRunRegex(), (match) => {
		return Array.from(match)[0] || "";
	}).replace(TRAILING_FORMATTABLE_WHITESPACE_RE, "");
}
//#endregion
//#region src/plugins/OpenLyric/domain/text-columns.ts
/**
* Columns in Open Lyric's plain-text layout, where a chord row sits over its
* lyric line in a monospace font. A chord's column is where its syllable
* starts *on screen*, not its UTF-16 index: marks that sit on a letter
* (Khmer vowel signs above or below, Thai tone marks, decomposed accents),
* invisible format characters (the zero-width word break U+200B, ZWNJ, ZWJ)
* and a Khmer subscript consonant — written COENG (U+17D2) + consonant,
* drawn under the letter before — take no column of their own. Every other
* character takes one.
*
* The text renderer measures with {@link getTextColumnWidth} and the
* plain-text import maps back with {@link getIndexAtTextColumn}, so a song
* rendered to text and imported again keeps its chords on their syllables.
*/
var ZERO_COLUMN_CHARACTER_RE = /^[\p{Mn}\p{Me}\p{Cf}]$/u;
var KHMER_COENG = "្";
/** Whether a character at `index` (a code point) takes no column. */
function isZeroColumnCharacter(characters, index) {
	const character = characters[index];
	return ZERO_COLUMN_CHARACTER_RE.test(character) || index > 0 && characters[index - 1] === KHMER_COENG;
}
/** The columns a text takes in a monospace chord-over-lyric layout. */
function getTextColumnWidth(text) {
	const characters = Array.from(String(text ?? ""));
	let width = 0;
	for (let index = 0; index < characters.length; index += 1) if (!isZeroColumnCharacter(characters, index)) width += 1;
	return width;
}
/**
* The UTF-16 index in `text` where something placed at `column` goes: before
* the first character that starts at or after that column — never between a
* letter and the marks drawn on it. Past the end of the text, the text's
* length (the caller pads to reach the column).
*/
function getIndexAtTextColumn(text, column) {
	const characters = Array.from(String(text ?? ""));
	let width = 0;
	let offset = 0;
	for (let index = 0; index < characters.length; index += 1) {
		const zeroColumn = isZeroColumnCharacter(characters, index);
		if (!zeroColumn && width >= column) return offset;
		if (!zeroColumn) width += 1;
		offset += characters[index].length;
	}
	return offset;
}
//#endregion
//#region src/plugins/OpenLyric/document/plain-text-import.ts
var DEFAULT_IMPORT_VALUES = {
	Artist: "Unknown Artist",
	Copyright: "Unknown",
	Key: Array.isArray(CONFIG_ENUM_FIELD_VALUES$1.Key) ? CONFIG_ENUM_FIELD_VALUES$1.Key[0] : "C",
	Tempo: "120bpm",
	Time: Array.isArray(CONFIG_ENUM_FIELD_VALUES$1.Time) ? CONFIG_ENUM_FIELD_VALUES$1.Time[0] : "4/4"
};
var SINGLE_PATTERN_RE = /^Strumming Pattern:\s*(.+)$/;
var MULTI_PATTERN_HEADER_RE = /^Strumming Patterns:\s*$/;
var STRUCTURE_LINE_RE = /^Structure:\s*(.+)$/;
var ZWSP_SINGLE_PATTERN_RE = /^Strumming Pattern:[\s\u200B]*(.+)$/u;
var ZWSP_MULTI_PATTERN_HEADER_RE = /^Strumming Patterns:[\s\u200B]*$/u;
var ZWSP_STRUCTURE_LINE_RE = /^Structure:[\s\u200B]*(.+)$/u;
var REPEAT_SUFFIX_RE = /^\(([1-9]\d*x)\)(?:\s+|$)/;
var ZWSP_REPEAT_SUFFIX_RE = /^\(([1-9]\d*x)\)(?:[\s\u200B]+|$)/u;
var SECTION_INDENT_RE = /^(?: {2}|\t)/;
var CONFIG_ENTRY_RE$1 = /^-\s*([^:]+):\s*(.*)$/;
var CHORD_PLACEMENT_RE = new RegExp(String.raw`^(\|?)(${CHORD_SYMBOL_SOURCE})`);
var SUPPORTED_PLAIN_TEXT_CONFIG_FIELDS = /* @__PURE__ */ new Set([
	"Description",
	"Copyright",
	"Theme",
	"Genre",
	"Style",
	"Keywords",
	"Year",
	"Melody",
	"Attachments"
]);
var STRUCTURE_CODE_BY_HEADER = new Map(STRUCTURE_TOKEN_DEFINITIONS.map(({ header, code }) => [header, code]));
var LYRIC_SECTION_NAME_SET = new Set(LYRIC_SECTION_NAMES);
/**
* Section labels other formats use, mapped onto the Open Lyric header that
* means the same thing.
*
* Conversion is the whole point of this table. ChordPro and OnSong let a
* section carry any label, so a chart arriving from either can name a part
* Open Lyric has no header for — and without a mapping the heading line is not
* recognised as a heading at all and gets absorbed into the previous section's
* body, which corrupts the song silently.
*
* Only near-synonyms are listed. Labels whose section-hood the research did not
* support (`Hook` and `Break` are a motif and a pause, `Key Change` is a
* production instruction) are mapped to the nearest section that can hold their
* content rather than being invented as fences. Keys are matched after
* `normalizeAliasKey`, so spacing, punctuation and case do not matter.
*/
var SECTION_NAME_ALIASES = new Map(Object.entries({
	ending: "Outro",
	coda: "Outro",
	out: "Outro",
	fine: "Outro",
	turnaround: "Turnaround",
	turn: "Turnaround",
	ta: "Turnaround",
	instr: "Instrumental",
	inst: "Instrumental",
	instrumentalbreak: "Instrumental",
	musicalinterlude: "Interlude",
	break: "Breakdown",
	drumbreak: "Breakdown",
	adlib: "Vamp",
	adlibs: "Vamp",
	free: "Vamp",
	chant: "Vamp",
	hook: "Refrain",
	posthook: "Post-Chorus",
	channel: "Pre-Chorus",
	build: "Pre-Chorus",
	lift: "Pre-Chorus",
	middle: "Bridge",
	middle8: "Bridge",
	middleeight: "Bridge",
	midsection: "Bridge",
	rap: "Verse",
	spoken: "Note",
	spokenword: "Note",
	keychange: "Note",
	modulation: "Note",
	prechorus: "Pre-Chorus",
	postchorus: "Post-Chorus",
	finalchorus: "Final-Chorus",
	lastchorus: "Final-Chorus",
	intro: "Intro",
	outro: "Outro",
	reprise: "Refrain"
}));
/**
* Case, spacing, punctuation and any trailing index removed.
*
* The soft hyphen and zero-width space are in the strip set because copying a
* chart out of a PDF or a Word document routinely leaves them inside a word.
*/
function normalizeAliasKey(value) {
	return String(value ?? "").toLowerCase().replace(/[\s­​._'’/-]+/gu, "").replace(/\d+$/, "");
}
function parseAliasedSectionName(partText, allowZwspSeparators = true) {
	const trimmedPartText = trimSpaceLikeText(partText, allowZwspSeparators);
	if (!trimmedPartText) return null;
	const indexMatch = trimmedPartText.match(/(\d+)\s*$/);
	const aliasKey = normalizeAliasKey(trimmedPartText);
	const targetHeader = SECTION_NAME_ALIASES.get(aliasKey);
	if (!targetHeader) return null;
	const indexText = indexMatch ? indexMatch[1].replace(/^0+/, "") : "";
	const parsedHeader = parseFenceHeader(indexText ? `${targetHeader} ${indexText}` : targetHeader) || parseFenceHeader(targetHeader);
	if (!parsedHeader) return null;
	return {
		originalPartText: trimmedPartText,
		parsedHeader
	};
}
function normalizeRawText(value) {
	return String(value ?? "").replace(/\uFEFF/g, "").replace(/\r\n?/g, "\n");
}
function trimLineEnd(line, allowZwspSeparators = true) {
	return trimSpaceLikeEnd(line, allowZwspSeparators);
}
function trimBlankEdges(lines, allowZwspSeparators = true) {
	const normalizedLines = Array.isArray(lines) ? lines.slice() : [];
	let startIndex = 0;
	let endIndex = normalizedLines.length;
	while (startIndex < endIndex && !trimSpaceLikeText(normalizedLines[startIndex], allowZwspSeparators)) startIndex += 1;
	while (endIndex > startIndex && !trimSpaceLikeText(normalizedLines[endIndex - 1], allowZwspSeparators)) endIndex -= 1;
	return normalizedLines.slice(startIndex, endIndex);
}
function sanitizeConfigValue(value, allowZwspSeparators = true) {
	return trimSpaceLikeText(value, allowZwspSeparators);
}
function normalizeSeparatorText(value, allowZwspSeparators = true) {
	return trimSpaceLikeText(collapseSpaceLikeText(value, " ", allowZwspSeparators), allowZwspSeparators);
}
function getSinglePatternRe(allowZwspSeparators) {
	return allowZwspSeparators ? ZWSP_SINGLE_PATTERN_RE : SINGLE_PATTERN_RE;
}
function getMultiPatternHeaderRe(allowZwspSeparators) {
	return allowZwspSeparators ? ZWSP_MULTI_PATTERN_HEADER_RE : MULTI_PATTERN_HEADER_RE;
}
function getStructureLineRe(allowZwspSeparators) {
	return allowZwspSeparators ? ZWSP_STRUCTURE_LINE_RE : STRUCTURE_LINE_RE;
}
function getRepeatSuffixRe(allowZwspSeparators) {
	return allowZwspSeparators ? ZWSP_REPEAT_SUFFIX_RE : REPEAT_SUFFIX_RE;
}
function stripSectionIndent(line) {
	return String(line ?? "").replace(SECTION_INDENT_RE, "");
}
function parseMetaEntriesFromLine(line, allowZwspSeparators = true) {
	return Array.from(normalizeSeparatorText(line, allowZwspSeparators).matchAll(/(?:^|,\s*)(Key|Time|Tempo):\s*([^,]+)(?=,\s*(?:Key|Time|Tempo):|$)/g)).map((match) => ({
		field: match[1],
		value: sanitizeConfigValue(match[2], allowZwspSeparators)
	}));
}
function isStructuredHeaderLine(line, allowZwspSeparators = true) {
	const trimmedLine = trimSpaceLikeText(line, allowZwspSeparators);
	return Boolean(trimmedLine && (parseMetaEntriesFromLine(trimmedLine, allowZwspSeparators).length || getSinglePatternRe(allowZwspSeparators).test(trimmedLine) || getMultiPatternHeaderRe(allowZwspSeparators).test(trimmedLine) || getStructureLineRe(allowZwspSeparators).test(trimmedLine)));
}
function parseSecondaryText(line, allowZwspSeparators = true) {
	const parts = String(line ?? "").split(" · ").map((segment) => sanitizeConfigValue(segment, allowZwspSeparators)).filter(Boolean);
	if (parts.length >= 2) return {
		subtitle: parts.slice(0, -1).join(" · "),
		artist: parts[parts.length - 1] || ""
	};
	return {
		subtitle: "",
		artist: sanitizeConfigValue(line, allowZwspSeparators)
	};
}
function parsePlainTextSectionHeading(line, allowZwspSeparators = true) {
	const rawLine = trimLineEnd(line, allowZwspSeparators);
	if (!rawLine || /^[ \t]/.test(rawLine)) return null;
	const colonIndex = rawLine.indexOf(":");
	if (colonIndex <= 0) return null;
	const partText = trimSpaceLikeText(rawLine.slice(0, colonIndex), allowZwspSeparators);
	const aliased = parseFenceHeader(partText) ? null : parseAliasedSectionName(partText, allowZwspSeparators);
	const parsedHeader = aliased?.parsedHeader || parseFenceHeader(partText);
	if (!parsedHeader || parsedHeader.header === "Config") return null;
	const renamedFrom = aliased && aliased.originalPartText !== parsedHeader.partName ? aliased.originalPartText : "";
	let remainder = trimSpaceLikeStart(rawLine.slice(colonIndex + 1), allowZwspSeparators);
	let repeatText = "";
	const repeatMatch = remainder.match(getRepeatSuffixRe(allowZwspSeparators));
	if (repeatMatch) {
		repeatText = repeatMatch[1];
		remainder = trimSpaceLikeStart(remainder.slice(repeatMatch[0].length), allowZwspSeparators);
	}
	return {
		inlineBody: remainder,
		parsedHeader,
		renamedFrom,
		repeatText
	};
}
function finalizeParsedSection(section, allowZwspSeparators = true) {
	return {
		...section,
		bodyLines: trimBlankEdges((section.bodyLines || []).map((line) => trimLineEnd(line, allowZwspSeparators)), allowZwspSeparators)
	};
}
function splitHeaderAndSections(lines, allowZwspSeparators = true) {
	const headerLines = [];
	const sections = [];
	let currentSection = null;
	let sawSection = false;
	(lines || []).forEach((line) => {
		const parsedHeading = parsePlainTextSectionHeading(line, allowZwspSeparators);
		if (parsedHeading) {
			sawSection = true;
			if (currentSection) sections.push(finalizeParsedSection(currentSection, allowZwspSeparators));
			currentSection = {
				...parsedHeading,
				bodyLines: parsedHeading.inlineBody ? [parsedHeading.inlineBody] : []
			};
			return;
		}
		if (!sawSection) {
			headerLines.push(line);
			return;
		}
		currentSection?.bodyLines.push(line);
	});
	if (currentSection) sections.push(finalizeParsedSection(currentSection, allowZwspSeparators));
	return {
		headerLines,
		sections
	};
}
function parseHeaderBlock(headerLines, { preferSecondaryText = true, allowZwspSeparators = true } = {}) {
	const lines = Array.isArray(headerLines) ? headerLines.map((line) => trimLineEnd(line, allowZwspSeparators)) : [];
	const meta = {
		Key: "",
		Tempo: "",
		Time: ""
	};
	const plainTextConfig = {
		Attachments: [],
		Copyright: "",
		Genre: "",
		Keywords: "",
		Melody: "",
		Style: "",
		Theme: "",
		Year: ""
	};
	const descriptionLines = [];
	const strummingLines = [];
	let title = "";
	let subtitle = "";
	let artist = "";
	let structureText = "";
	let signalCount = 0;
	let index = 0;
	while (index < lines.length && !trimSpaceLikeText(lines[index], allowZwspSeparators)) index += 1;
	if (index < lines.length) {
		title = sanitizeConfigValue(lines[index], allowZwspSeparators);
		if (title) signalCount += 1;
		index += 1;
	}
	while (index < lines.length && !trimSpaceLikeText(lines[index], allowZwspSeparators)) index += 1;
	if (preferSecondaryText && index < lines.length && trimSpaceLikeText(lines[index], allowZwspSeparators) && !isStructuredHeaderLine(lines[index], allowZwspSeparators)) {
		const parsedSecondary = parseSecondaryText(lines[index], allowZwspSeparators);
		subtitle = parsedSecondary.subtitle;
		artist = parsedSecondary.artist;
		signalCount += 1;
		index += 1;
	}
	while (index < lines.length) {
		const rawLine = lines[index];
		const trimmedLine = trimSpaceLikeText(rawLine, allowZwspSeparators);
		if (!trimmedLine) {
			index += 1;
			continue;
		}
		const metaEntries = parseMetaEntriesFromLine(trimmedLine, allowZwspSeparators);
		if (metaEntries.length) {
			metaEntries.forEach(({ field, value }) => {
				meta[field] = value;
			});
			signalCount += metaEntries.length;
			index += 1;
			continue;
		}
		const singlePatternMatch = trimmedLine.match(getSinglePatternRe(allowZwspSeparators));
		if (singlePatternMatch) {
			strummingLines.push(trimSpaceLikeText(singlePatternMatch[1], allowZwspSeparators));
			signalCount += 1;
			index += 1;
			continue;
		}
		if (getMultiPatternHeaderRe(allowZwspSeparators).test(trimmedLine)) {
			signalCount += 1;
			index += 1;
			while (index < lines.length) {
				const continuationLine = lines[index];
				if (!trimSpaceLikeText(continuationLine, allowZwspSeparators)) {
					index += 1;
					continue;
				}
				if (!/^[ \t]/.test(continuationLine)) break;
				strummingLines.push(trimSpaceLikeText(continuationLine, allowZwspSeparators));
				index += 1;
			}
			continue;
		}
		const structureMatch = trimmedLine.match(getStructureLineRe(allowZwspSeparators));
		if (structureMatch) {
			structureText = normalizeSeparatorText(structureMatch[1], allowZwspSeparators);
			signalCount += 1;
			index += 1;
			continue;
		}
		const configEntryMatch = trimmedLine.match(CONFIG_ENTRY_RE$1);
		if (configEntryMatch) {
			const field = normalizeConfigFieldName(configEntryMatch[1]);
			if (SUPPORTED_PLAIN_TEXT_CONFIG_FIELDS.has(field)) {
				const initialValue = sanitizeConfigValue(configEntryMatch[2], allowZwspSeparators);
				signalCount += 1;
				if (field === "Description" || field === "Attachments") {
					const targetLines = field === "Description" ? descriptionLines : plainTextConfig.Attachments;
					if (initialValue) targetLines.push(initialValue);
					index += 1;
					while (index < lines.length) {
						const continuationLine = lines[index];
						if (!trimSpaceLikeText(continuationLine, allowZwspSeparators)) {
							index += 1;
							continue;
						}
						if (!/^[ \t]/.test(continuationLine)) break;
						targetLines.push(sanitizeConfigValue(continuationLine, allowZwspSeparators));
						index += 1;
					}
					continue;
				}
				plainTextConfig[field] = initialValue;
				index += 1;
				continue;
			}
		}
		descriptionLines.push(trimmedLine);
		index += 1;
	}
	return {
		artist,
		attachmentLines: plainTextConfig.Attachments,
		copyright: plainTextConfig.Copyright,
		descriptionLines,
		genre: plainTextConfig.Genre,
		keywords: plainTextConfig.Keywords,
		melody: plainTextConfig.Melody,
		meta,
		signalCount,
		style: plainTextConfig.Style,
		strummingLines,
		structureText,
		subtitle,
		theme: plainTextConfig.Theme,
		title,
		year: plainTextConfig.Year
	};
}
function normalizeStrummingConfigLines(rawLines, allowZwspSeparators = true) {
	const configLines = [];
	(rawLines || []).forEach((rawLine) => {
		const trimmedLine = trimSpaceLikeText(normalizeStrummingPatternValue(rawLine, allowZwspSeparators), allowZwspSeparators);
		if (!trimmedLine) return;
		const labeledPatternMatch = trimmedLine.match(/^([^:]+):\s*(.+)$/);
		if (labeledPatternMatch && isValidStrummingPatternValue(trimSpaceLikeText(labeledPatternMatch[2], allowZwspSeparators), allowZwspSeparators)) {
			const label = sanitizeConfigValue(labeledPatternMatch[1], allowZwspSeparators);
			const pattern = normalizeStrummingPatternValue(labeledPatternMatch[2], allowZwspSeparators).trim();
			if (label) configLines.push(`  // ${label}`);
			configLines.push(`  ${pattern}`);
			return;
		}
		configLines.push(`  ${trimmedLine}`);
	});
	return configLines;
}
function parseRepeatCount(repeatText) {
	const match = String(repeatText ?? "").match(/^([1-9]\d*)x$/);
	return match ? Number.parseInt(match[1], 10) : 1;
}
function createStructureToken(parsedHeader, repeatText = "") {
	const structureCode = STRUCTURE_CODE_BY_HEADER.get(parsedHeader?.header);
	if (!structureCode) return "";
	const repeatCount = parseRepeatCount(repeatText);
	return `${structureCode}${parsedHeader.indexText || ""}${repeatCount > 1 ? `x${repeatCount}` : ""}`;
}
function parseChordPlacements(line, allowZwspSeparators = true) {
	const source = String(line ?? "");
	const placements = [];
	let offset = 0;
	while (offset < source.length) {
		if (isSpaceLikeCharacter(source[offset], allowZwspSeparators)) {
			offset += 1;
			continue;
		}
		const match = source.slice(offset).match(CHORD_PLACEMENT_RE);
		if (!match) return null;
		placements.push({
			chord: match[2],
			leadingBar: Boolean(match[1]),
			position: offset
		});
		offset += match[0].length;
	}
	return placements.length ? placements : null;
}
function mergeChordPlacementLineWithLyrics(chordLine, lyricLine, allowZwspSeparators = true) {
	const placements = parseChordPlacements(chordLine, allowZwspSeparators);
	if (!placements) return null;
	let mergedLine = String(lyricLine ?? "");
	placements.slice().sort((left, right) => right.position - left.position).forEach(({ chord, leadingBar, position }) => {
		const lyricWidth = getTextColumnWidth(mergedLine);
		if (position > lyricWidth) mergedLine = `${mergedLine}${" ".repeat(position - lyricWidth)}`;
		const index = getIndexAtTextColumn(mergedLine, position);
		const insertion = `${leadingBar ? "|" : ""}[${chord}]`;
		mergedLine = `${mergedLine.slice(0, index)}${insertion}${mergedLine.slice(index)}`;
	});
	return trimLineEnd(mergedLine, allowZwspSeparators);
}
function createSectionMarkdownLines(section, allowZwspSeparators = true) {
	const bodyLines = trimBlankEdges((section.bodyLines || []).map((line) => trimLineEnd(line, allowZwspSeparators)), allowZwspSeparators);
	const markdownLines = section.renamedFrom ? [`// ${section.renamedFrom}`] : [];
	const isLyricSection = LYRIC_SECTION_NAME_SET.has(section.parsedHeader?.header);
	for (let index = 0; index < bodyLines.length; index += 1) {
		const currentLine = stripSectionIndent(bodyLines[index]);
		if (isLyricSection && index < bodyLines.length - 1) {
			const mergedLine = mergeChordPlacementLineWithLyrics(currentLine, stripSectionIndent(bodyLines[index + 1]), allowZwspSeparators);
			if (mergedLine !== null) {
				markdownLines.push(mergedLine);
				index += 1;
				continue;
			}
		}
		markdownLines.push(currentLine);
	}
	return trimBlankEdges(markdownLines, allowZwspSeparators);
}
function dedupeSections(sections, allowZwspSeparators = true) {
	const uniqueSections = [];
	const sectionBodiesByPartName = /* @__PURE__ */ new Map();
	let hasConflictingDuplicates = false;
	(sections || []).forEach((section) => {
		const partName = section.parsedHeader?.partName || "";
		if (!partName) return;
		const bodyText = createSectionMarkdownLines(section, allowZwspSeparators).join("\n");
		const previousBodyText = sectionBodiesByPartName.get(partName);
		if (typeof previousBodyText === "string") {
			if (previousBodyText !== bodyText) hasConflictingDuplicates = true;
			return;
		}
		sectionBodiesByPartName.set(partName, bodyText);
		uniqueSections.push({
			bodyText,
			partName
		});
	});
	return {
		hasConflictingDuplicates,
		uniqueSections
	};
}
function createStructuredSectionsFromPlainTextStructure(structureText, allowZwspSeparators = true) {
	const normalizedStructureText = normalizeSeparatorText(structureText, allowZwspSeparators);
	if (!normalizedStructureText) return [];
	const segments = normalizedStructureText.split(/\s+-\s+/).map((segment) => normalizeSeparatorText(segment, allowZwspSeparators)).filter(Boolean);
	if (!segments.length) return [];
	const structuredSections = [];
	for (const segment of segments) {
		const repeatMatch = segment.match(/^(.*?)(?:\s+\(([1-9]\d*x)\))?$/);
		const partText = normalizeSeparatorText(repeatMatch?.[1] || segment, allowZwspSeparators);
		const repeatText = normalizeSeparatorText(repeatMatch?.[2] || "", allowZwspSeparators);
		const parsedHeader = parseFenceHeader(partText);
		if (!parsedHeader || parsedHeader.header === "Config") return [];
		structuredSections.push({
			bodyLines: [],
			inlineBody: "",
			parsedHeader,
			repeatText
		});
	}
	return structuredSections;
}
function createFallbackSection(text, allowZwspSeparators = true) {
	const parsedHeader = parseFenceHeader("Breakdown 1");
	if (!parsedHeader) return null;
	return {
		bodyLines: trimBlankEdges(normalizeRawText(text).split("\n").map((line) => trimLineEnd(line, allowZwspSeparators)), allowZwspSeparators),
		inlineBody: "",
		parsedHeader,
		repeatText: ""
	};
}
function createSectionMarkdownBlock(partName, bodyText) {
	return bodyText ? [
		`\`\`\`ol:${partName}`,
		bodyText,
		"```"
	].join("\n") : [`\`\`\`ol:${partName}`, "```"].join("\n");
}
function parseOpenLyricPlainText(rawText) {
	const normalizedText = normalizeRawText(rawText);
	const allowZwspSeparators = shouldAllowInvisibleWordSeparators(normalizedText);
	const { headerLines, sections: parsedSections } = splitHeaderAndSections(normalizedText.split("\n"), allowZwspSeparators);
	const hasStructuredHeaderSignal = headerLines.some((line) => {
		return isStructuredHeaderLine(line, allowZwspSeparators);
	});
	const header = parseHeaderBlock(headerLines, {
		allowZwspSeparators,
		preferSecondaryText: Boolean(parsedSections.length || hasStructuredHeaderSignal)
	});
	const structuredSections = !parsedSections.length ? createStructuredSectionsFromPlainTextStructure(header.structureText, allowZwspSeparators) : [];
	const fallbackSection = !parsedSections.length && !structuredSections.length && trimSpaceLikeText(normalizedText, allowZwspSeparators) ? createFallbackSection(normalizedText, allowZwspSeparators) : null;
	const sections = parsedSections.length ? parsedSections : structuredSections.length ? structuredSections : fallbackSection ? [fallbackSection] : [];
	const structureTokens = (parsedSections.length ? parsedSections : structuredSections).map((section) => createStructureToken(section.parsedHeader, section.repeatText)).filter(Boolean);
	const { hasConflictingDuplicates, uniqueSections } = dedupeSections(sections, allowZwspSeparators);
	const renamedSections = sections.filter((section) => section.renamedFrom).map((section) => ({
		from: section.renamedFrom,
		to: section.parsedHeader.partName
	}));
	const placeholdersUsed = [];
	const title = sanitizeConfigValue(header.title, allowZwspSeparators) || "Untitled Song";
	if (!sanitizeConfigValue(header.title, allowZwspSeparators)) placeholdersUsed.push("Title");
	const subtitle = sanitizeConfigValue(header.subtitle, allowZwspSeparators);
	const artistSource = sanitizeConfigValue(header.artist, allowZwspSeparators);
	const artist = artistSource || DEFAULT_IMPORT_VALUES.Artist;
	if (!artistSource) placeholdersUsed.push("Artist");
	const keySource = sanitizeConfigValue(header.meta.Key, allowZwspSeparators);
	const key = keySource || DEFAULT_IMPORT_VALUES.Key;
	if (!keySource) placeholdersUsed.push("Key");
	const tempoSource = sanitizeConfigValue(header.meta.Tempo, allowZwspSeparators);
	const tempo = tempoSource || DEFAULT_IMPORT_VALUES.Tempo;
	if (!tempoSource) placeholdersUsed.push("Tempo");
	const timeSource = sanitizeConfigValue(header.meta.Time, allowZwspSeparators);
	const time = timeSource || DEFAULT_IMPORT_VALUES.Time;
	if (!timeSource) placeholdersUsed.push("Time");
	const descriptionLines = trimBlankEdges(header.descriptionLines.map((line) => sanitizeConfigValue(line, allowZwspSeparators)), allowZwspSeparators);
	const copyrightSource = sanitizeConfigValue(header.copyright, allowZwspSeparators);
	const copyright = copyrightSource || DEFAULT_IMPORT_VALUES.Copyright;
	if (!copyrightSource) placeholdersUsed.push("Copyright");
	const theme = sanitizeConfigValue(header.theme, allowZwspSeparators);
	const genre = sanitizeConfigValue(header.genre, allowZwspSeparators);
	const style = sanitizeConfigValue(header.style, allowZwspSeparators);
	const keywords = sanitizeConfigValue(header.keywords, allowZwspSeparators);
	const year = sanitizeConfigValue(header.year, allowZwspSeparators);
	const melody = sanitizeConfigValue(header.melody, allowZwspSeparators);
	const attachmentLines = (header.attachmentLines || []).map((line) => sanitizeConfigValue(line, allowZwspSeparators)).filter(Boolean);
	const strummingLines = normalizeStrummingConfigLines(header.strummingLines, allowZwspSeparators);
	const structureValue = structureTokens.join("") || "D1";
	if (!structureTokens.length) placeholdersUsed.push("Structure");
	const configLines = ["```ol:Config", `- Title: ${title}`];
	if (subtitle) configLines.push(`- Subtitle: ${subtitle}`);
	if (descriptionLines.length) {
		configLines.push("- Description:");
		descriptionLines.forEach((line) => {
			configLines.push(`  ${line}`);
		});
	}
	configLines.push(`- Artist: ${artist}`);
	configLines.push(`- Copyright: ${copyright}`);
	configLines.push(`- Key: ${key}`);
	configLines.push(`- Tempo: ${tempo}`);
	configLines.push(`- Time: ${time}`);
	if (theme) configLines.push(`- Theme: ${theme}`);
	configLines.push(`- Structure: ${structureValue}`);
	if (genre) configLines.push(`- Genre: ${genre}`);
	if (style) configLines.push(`- Style: ${style}`);
	if (keywords) configLines.push(`- Keywords: ${keywords}`);
	if (year) configLines.push(`- Year: ${year}`);
	if (melody) configLines.push(`- Melody: ${melody}`);
	if (attachmentLines.length) {
		configLines.push("- Attachments:");
		attachmentLines.forEach((line) => {
			configLines.push(`  ${line}`);
		});
	}
	if (strummingLines.length) {
		configLines.push("- Strumming Patterns:");
		configLines.push(...strummingLines);
	}
	configLines.push("```");
	const markdown = [configLines.join("\n"), ...uniqueSections.map(({ bodyText, partName }) => {
		return createSectionMarkdownBlock(partName, bodyText);
	})].filter(Boolean).join("\n\n").trim();
	const recognizableSignalCount = header.signalCount + parsedSections.length;
	return {
		hasConflictingDuplicates,
		markdown,
		renamedSections,
		matchesPlainTextFormat: !fallbackSection && !hasConflictingDuplicates && (parsedSections.length > 0 || structuredSections.length > 0 || recognizableSignalCount >= 3),
		placeholdersUsed
	};
}
//#endregion
//#region src/plugins/OpenLyric/preview/controller/constants.ts
var ATTACHMENT_URL_SCHEME_SOURCE = String.raw`[A-Za-z][A-Za-z0-9+.-]*:\/\/`;
var ATTACHMENT_SOURCE_URL_SOURCE = String.raw`(?:${ATTACHMENT_URL_SCHEME_SOURCE}\S[^\r\n]*)`;
var ATTACHMENT_MARKDOWN_URL_SOURCE = String.raw`(?:${ATTACHMENT_URL_SCHEME_SOURCE}\S[^\r\n)]*)`;
var ATTACHMENT_VALUE_SOURCE = String.raw`(?:${ATTACHMENT_SOURCE_URL_SOURCE}|\[[^\]\r\n]+\]\(${ATTACHMENT_MARKDOWN_URL_SOURCE}\))`;
new RegExp(`^${ATTACHMENT_VALUE_SOURCE}$`);
var STRUCTURE_DEFINITIONS_BY_HEADER = new Map(STRUCTURE_TOKEN_DEFINITIONS.map((definition) => [definition.header, definition]));
var OPEN_LYRIC_EXPORT_CONTROL_SELECTOR = ".ol-song-view__structure-key-control, .ol-song-view__simplify-toggle";
Object.freeze({
	type: "png-image",
	isWithInfo: false,
	width: 1920,
	height: 1080,
	backgroundAlpha: 1,
	fontSize: 48
});
var OPEN_LYRIC_POWERPOINT_DEFAULT_TYPOGRAPHY = Object.freeze({
	chromeFontFace: "Arial",
	lyricFontFace: "Courier New",
	lyricFontSize: 24
});
//#endregion
//#region src/plugins/OpenLyric/preview/controller/section-naming.ts
/**
* Creating, naming and removing sections from the rendered preview.
*
* Three affordances, one mechanism. "Add Lyric" — the control `OLConfig` renders
* in the gap under the Config card — opens a picker for the section type and
* its number, and writes a new ```` ```ol:Verse 3 ```` fence after the last
* fence in the document. The tag beside a section card's title opens the same
* picker over that section's existing name, and rewrites its header line.
*
* Both are text edits through `replaceDocumentLineRange`, never DOM mutations
* the preview keeps, so the panels, the text panel and the undo stack stay in
* step — the rule `section-editing.ts` and `config-text-editing.ts` already
* follow.
*
* The section-type list comes from `OLFenceRegistry`, so a fence added to the
* language appears in the picker without an edit here, and a name the picker
* can produce is always a name the parser accepts: the reader picks a header
* and a number rather than typing notation, and a name already declared is
* refused before the write rather than left as an invisible "Duplicate ol
* part" marker.
*
* A rename — and a delete — carries the song's running order with it: every
* `- Structure:` step naming the part is rewritten or removed in the *same*
* document edit, so neither can silently leave `V1` pointing at a part that no
* longer exists. That orphan is a real diagnostic ("Structure references
* undeclared ol part", `document/validation.ts`) and one a preview-only reader
* cannot see, which is why carrying the running order is not optional here.
* Deleting is the one destructive gesture in the preview, so it asks first, and
* the question names how many running-order steps go with the section.
*
* Markdown panel only. The lyric/presentation panel shares these delegated
* listeners, so every lookup here is scoped to `refs.preview`.
*/
/** `  ```ol:Verse 1  ` → the ```` ```ol: ```` prefix and the header info. */
var FENCE_HEADER_LINE_RE = /^(\s*```ol:)([^\r\n]*?)[ \t]*$/;
/** `- Structure:   IV1CO` → prefix, field name, separator, value. */
var CONFIG_FIELD_LINE_RE$1 = /^(\s*-\s*([^:]+):)([ \t]*)(.*)$/;
function splitLines$1(text) {
	return String(text ?? "").replace(/\r\n?/g, "\n").split("\n");
}
/**
* Every section type the language defines, in registry order.
*
* `Config` is excluded: it is metadata, it is required, and exactly one of it
* may exist — none of which the "add a section" gesture means.
*/
function getSectionTypeOptions() {
	return registry.getDefinitions().filter((definition) => definition.header !== "Config").map((definition) => ({
		header: definition.header,
		allowsNumbering: Boolean(definition.allowsNumbering),
		allowsDuplicates: Boolean(definition.allowsDuplicateDeclaredPart?.()),
		description: definition.description || ""
	}));
}
/** The part names the document already declares — `Config` aside. */
function collectDeclaredSectionPartNames(markdown) {
	const partNames = /* @__PURE__ */ new Set();
	parseOpenLyricFences(markdown).forEach((fence) => {
		const partName = String(fence.parsedHeader?.partName ?? "");
		if (partName && fence.parsedHeader?.header !== "Config") partNames.add(partName);
	});
	return partNames;
}
/**
* The lowest index this header has no fence for yet.
*
* `Verse 1` and `Verse 2` present means the reader is offered `Verse 3` — the
* number they were going to type anyway, and the one that cannot collide.
*/
function getNextFreeSectionIndexText(declaredPartNames, header, option) {
	if (!option?.allowsNumbering) return "";
	let index = 1;
	while (declaredPartNames.has(formatDeclaredPartName(header, String(index)))) index += 1;
	return String(index);
}
/**
* The document edit that adds an empty section.
*
* It lands after the last fence in the document rather than at the click's own
* position: a song grows at the end, and inserting under `Config` would build
* every song backwards. Returns `null` when the name is not one the parser
* accepts, so a picker that somehow produced nonsense writes nothing.
*/
function buildSectionInsertion(markdown, partName) {
	const parsedHeader = parseFenceHeader(String(partName ?? "").trim());
	if (!parsedHeader?.partName) return null;
	const lines = splitLines$1(markdown);
	const fences = parseOpenLyricFences(markdown);
	const lastFence = fences.length ? fences[fences.length - 1] : null;
	let anchorLineNumber = lastFence ? lastFence.endLineNumber : lines.length;
	if (!lastFence) while (anchorLineNumber > 0 && !lines[anchorLineNumber - 1].trim()) anchorLineNumber -= 1;
	const anchorLine = lines[anchorLineNumber - 1] ?? "";
	const nextLines = [`\`\`\`ol:${parsedHeader.partName}`, "```"];
	if (anchorLine.trim()) nextLines.unshift("");
	return {
		startLineNumber: anchorLineNumber + 1,
		endLineNumber: anchorLineNumber,
		nextLines,
		partName: parsedHeader.partName
	};
}
/**
* The fence's opening line as it should read once renamed, or `null`.
*
* `expectedPartName` is the name the control was rendered with; the line is
* refused when it no longer declares it, so markup a re-render left behind
* renames nothing. The indentation and the ```` ```ol: ```` prefix the document
* already had are always preserved — a rename can only ever replace the header
* info.
*/
function buildRenamedFenceHeaderLine(sourceLine, expectedPartName, nextPartName) {
	const headerMatch = String(sourceLine ?? "").match(FENCE_HEADER_LINE_RE);
	if (!headerMatch) return null;
	const currentHeader = parseFenceHeader(headerMatch[2].trim());
	if (!currentHeader?.partName || currentHeader.partName !== expectedPartName) return null;
	const nextHeader = parseFenceHeader(String(nextPartName ?? "").trim());
	if (!nextHeader?.partName || nextHeader.header === "Config") return null;
	return `${headerMatch[1]}${nextHeader.partName}`;
}
/**
* Where the `Config` fence declares `- Structure:`, if it declares it on one
* line. A value continued onto a second line is left alone rather than
* half-rewritten.
*/
function findConfigStructureFieldLine(markdown) {
	const configFence = parseOpenLyricFences(markdown).find((fence) => fence.parsedHeader?.header === "Config");
	if (!configFence) return null;
	const lines = splitLines$1(markdown);
	for (let lineNumber = configFence.startLineNumber + 1; lineNumber < configFence.endLineNumber; lineNumber += 1) {
		const fieldMatch = String(lines[lineNumber - 1] ?? "").match(CONFIG_FIELD_LINE_RE$1);
		if (!fieldMatch) continue;
		if (normalizeConfigFieldName(fieldMatch[2].trim()) !== "Structure") continue;
		const followingLine = String(lines[lineNumber] ?? "");
		if (lineNumber + 1 < configFence.endLineNumber && followingLine.trim() && !CONFIG_FIELD_LINE_RE$1.test(followingLine)) return null;
		return {
			lineNumber,
			prefix: fieldMatch[1],
			separator: fieldMatch[3],
			valueText: fieldMatch[4].replace(/\s+$/, "")
		};
	}
	return null;
}
/**
* The `- Structure:` line with every step naming `partName` re-coded to
* `nextPartName`, and how many steps that was.
*
* Each step keeps whatever followed its code in the source — a repeat suffix
* such as `x2` — so renaming a part never quietly drops a repeat. A value the
* structure parser cannot read, or a part with no structure code of its own, is
* left untouched (`null`): a rename must not be the thing that rewrites a
* `Structure` the reader has not fixed yet.
*/
function buildRenamedStructureLine(sourceLine, partName, nextPartName) {
	const fieldMatch = String(sourceLine ?? "").match(CONFIG_FIELD_LINE_RE$1);
	if (!fieldMatch) return null;
	if (normalizeConfigFieldName(fieldMatch[2].trim()) !== "Structure") return null;
	const nextHeader = parseFenceHeader(String(nextPartName ?? "").trim());
	const nextDefinition = nextHeader ? STRUCTURE_DEFINITIONS_BY_HEADER.get(nextHeader.header) : null;
	if (!nextDefinition) return null;
	const parsedStructure = parseStructureValue(fieldMatch[4].replace(/\s+$/, ""));
	if (parsedStructure.error) return null;
	const nextToken = `${nextDefinition.code}${nextDefinition.allowsNumbering ? nextHeader.indexText || "" : ""}`;
	const source = parsedStructure.text;
	let nextValue = "";
	let cursor = 0;
	let changedCount = 0;
	parsedStructure.steps.forEach((step) => {
		if (step.partName !== partName) return;
		const rawSuffix = String(step.rawText ?? "").slice(String(step.code ?? "").length + String(step.indexText ?? "").length);
		nextValue += source.slice(cursor, step.startOffset) + nextToken + rawSuffix;
		cursor = step.endOffset;
		changedCount += 1;
	});
	if (!changedCount) return null;
	nextValue += source.slice(cursor);
	if (parseStructureValue(nextValue).error) return null;
	return {
		changedCount,
		line: `${fieldMatch[1]}${fieldMatch[3] || " "}${nextValue}`
	};
}
/**
* The one document edit a rename is: the fence's opening line, plus the
* `- Structure:` line when it names the part, and every line between them
* written back unchanged.
*
* One range rather than two writes is the whole point — one user action stays
* one undo step, and the document can never be left half-renamed.
*/
function buildSectionRenameEdit(markdown, headerLineNumber, partName, nextPartName) {
	const lines = splitLines$1(markdown);
	const headerLine = lines[headerLineNumber - 1];
	if (headerLine === void 0) return null;
	const nextHeaderLine = buildRenamedFenceHeaderLine(headerLine, partName, nextPartName);
	if (nextHeaderLine === null) return null;
	const structureField = findConfigStructureFieldLine(markdown);
	const structureRewrite = structureField && structureField.lineNumber !== headerLineNumber ? buildRenamedStructureLine(lines[structureField.lineNumber - 1], partName, nextPartName) : null;
	if (!structureField || !structureRewrite) return {
		startLineNumber: headerLineNumber,
		endLineNumber: headerLineNumber,
		nextLines: [nextHeaderLine],
		structureStepCount: 0
	};
	const startLineNumber = Math.min(headerLineNumber, structureField.lineNumber);
	const endLineNumber = Math.max(headerLineNumber, structureField.lineNumber);
	const nextLines = lines.slice(startLineNumber - 1, endLineNumber);
	nextLines[headerLineNumber - startLineNumber] = nextHeaderLine;
	nextLines[structureField.lineNumber - startLineNumber] = structureRewrite.line;
	return {
		startLineNumber,
		endLineNumber,
		nextLines,
		structureStepCount: structureRewrite.changedCount
	};
}
/** A step's repeat count as a number — `Cx2` is 2, a bare `C` is 1. */
function getStructureStepRepeatCount(step) {
	const repeatMatch = String(step?.repeatText ?? "").match(/^(\d+)x$/);
	return repeatMatch ? Number.parseInt(repeatMatch[1], 10) : 1;
}
/**
* The `- Structure:` line with every step naming `partName` taken out, and how
* many steps that was.
*
* The surviving steps are re-emitted from their parsed parts rather than
* spliced out of the raw text, because removing a step can leave its two
* neighbours identical and adjacent — `V1CV1` minus the `Chorus` is the verse
* sung twice, which the notation spells `V1x2`, not `V1V1` (that is the
* "cannot place X twice in a row" diagnostic). Merging sums the repeat counts,
* so the song still runs the same number of times.
*
* An emptied value keeps the field declared (`- Structure:` with nothing after
* it), the same thing clearing a free-text `Config` field does — and an empty
* `Structure` is not a diagnostic, since the validator only checks the value
* when there is one.
*/
function buildRemovedStructureLine(sourceLine, partName) {
	const fieldMatch = String(sourceLine ?? "").match(CONFIG_FIELD_LINE_RE$1);
	if (!fieldMatch) return null;
	if (normalizeConfigFieldName(fieldMatch[2].trim()) !== "Structure") return null;
	const parsedStructure = parseStructureValue(fieldMatch[4].replace(/\s+$/, ""));
	if (parsedStructure.error) return null;
	const survivingSteps = [];
	let removedStepCount = 0;
	parsedStructure.steps.forEach((step) => {
		if (step.partName === partName) {
			removedStepCount += 1;
			return;
		}
		const previousStep = survivingSteps[survivingSteps.length - 1];
		if (previousStep && previousStep.partName === step.partName) {
			previousStep.repeatCount += getStructureStepRepeatCount(step);
			return;
		}
		survivingSteps.push({
			partName: step.partName,
			code: step.code,
			indexText: step.definition?.allowsNumbering ? step.indexText || "" : "",
			repeatCount: getStructureStepRepeatCount(step)
		});
	});
	if (!removedStepCount) return null;
	const nextValue = survivingSteps.map((step) => `${step.code}${step.indexText}${step.repeatCount > 1 ? `x${step.repeatCount}` : ""}`).join("");
	const reparsedStructure = parseStructureValue(nextValue);
	if (reparsedStructure.error || findAdjacentDuplicateStructureError(reparsedStructure.steps)) return null;
	return {
		removedStepCount,
		line: `${fieldMatch[1]}${nextValue ? fieldMatch[3] || " " : ""}${nextValue}`
	};
}
/**
* The one document edit a delete is: the fence's whole source range, one blank
* line beside it, and the `- Structure:` line when it names the part — with
* every line between them written back unchanged.
*
* One range rather than two writes, for the same reason the rename uses one:
* one user action stays one undo step, and the song can never be left with a
* running order pointing at a section that is gone.
*
* Refuses (`null`) when the range no longer opens and closes this fence, so a
* control left behind by stale markup deletes nothing.
*/
function buildSectionDeleteEdit(markdown, fenceStartLineNumber, fenceEndLineNumber, partName) {
	const lines = splitLines$1(markdown);
	const fenceStart = Math.trunc(Number(fenceStartLineNumber) || 0);
	const fenceEnd = Math.trunc(Number(fenceEndLineNumber) || 0);
	if (fenceStart < 1 || fenceEnd < fenceStart || fenceEnd > lines.length) return null;
	if (buildRenamedFenceHeaderLine(lines[fenceStart - 1], partName, partName) === null) return null;
	if (!/^\s*```\s*$/.test(lines[fenceEnd - 1])) return null;
	let removeStart = fenceStart;
	let removeEnd = fenceEnd;
	if (fenceStart > 1 && !lines[fenceStart - 2].trim()) removeStart = fenceStart - 1;
	else if (fenceEnd < lines.length && !lines[fenceEnd].trim()) removeEnd = fenceEnd + 1;
	const structureField = findConfigStructureFieldLine(markdown);
	const structureRewrite = structureField && (structureField.lineNumber < removeStart || structureField.lineNumber > removeEnd) ? buildRemovedStructureLine(lines[structureField.lineNumber - 1], partName) : null;
	if (!structureField || !structureRewrite) return {
		startLineNumber: removeStart,
		endLineNumber: removeEnd,
		nextLines: [],
		structureStepCount: 0
	};
	const startLineNumber = Math.min(removeStart, structureField.lineNumber);
	const endLineNumber = Math.max(removeEnd, structureField.lineNumber);
	const nextLines = [];
	for (let lineNumber = startLineNumber; lineNumber <= endLineNumber; lineNumber += 1) {
		if (lineNumber >= removeStart && lineNumber <= removeEnd) continue;
		nextLines.push(lineNumber === structureField.lineNumber ? structureRewrite.line : lines[lineNumber - 1]);
	}
	return {
		startLineNumber,
		endLineNumber,
		nextLines,
		structureStepCount: structureRewrite.removedStepCount
	};
}
//#endregion
//#region src/open-lyric-mcp/operations/text.ts
/** Small text helpers the operations share. */
function normalizeNewlines$3(value) {
	return String(value ?? "").replace(/\r\n?/g, "\n");
}
function splitLines(value) {
	return normalizeNewlines$3(value).split("\n");
}
/** Count the 1-based line numbers whose text differs between two documents. */
function countChangedLines(before, after) {
	const beforeLines = splitLines(before);
	const afterLines = splitLines(after);
	const length = Math.max(beforeLines.length, afterLines.length);
	let changed = 0;
	for (let index = 0; index < length; index += 1) if (beforeLines[index] !== afterLines[index]) changed += 1;
	return changed;
}
var SongOperationError = class extends Error {};
//#endregion
//#region src/open-lyric-mcp/operations/editing.ts
function withValidation(text, extra) {
	return {
		text,
		validation: validateSong(text),
		...extra
	};
}
var STRUCTURE_CODES_BY_HEADER = new Map(STRUCTURE_TOKEN_DEFINITIONS.map((definition) => [definition.header, definition.code]));
/**
* The Structure that plays `sections` once each, in order: `V1`, `C`, … with
* adjacent repeats of one part merged into a repeat count (`Cx2`).
*/
function deriveStructure(sections) {
	const steps = [];
	sections.forEach((section) => {
		const code = STRUCTURE_CODES_BY_HEADER.get(String(section.header ?? ""));
		if (!code) return;
		const token = `${code}${section.index ?? ""}`;
		const last = steps[steps.length - 1];
		if (last && last.token === token) last.count += 1;
		else steps.push({
			token,
			count: 1
		});
	});
	return steps.map(({ token, count }) => count > 1 ? `${token}x${count}` : token).join("");
}
function normalizeTempo(tempo) {
	if (tempo === void 0 || tempo === null || tempo === "") return;
	const text = String(tempo).trim();
	return /^\d+$/.test(text) ? `${text}bpm` : text;
}
function createSong(input) {
	if (!String(input?.title ?? "").trim()) throw new SongOperationError("A song needs a title.");
	const sections = (input.sections?.length ? input.sections : [{
		header: "Verse",
		index: 1,
		lines: []
	}]).map((section) => {
		const result = {
			header: String(section.header ?? "").trim(),
			lines: Array.isArray(section.lines) ? section.lines.map(String) : []
		};
		if (section.index !== void 0 && section.index !== null) result.index = Number(section.index);
		return result;
	});
	const song = {
		config: {
			Title: String(input.title).trim(),
			Structure: String(input.structure ?? "").trim() || deriveStructure(sections),
			Subtitle: input.subtitle,
			Description: typeof input.description === "string" ? splitLines(input.description) : input.description,
			Artist: input.artist,
			Copyright: input.copyright,
			Locales: input.locales,
			Key: input.key,
			Tempo: normalizeTempo(input.tempo),
			Time: input.time,
			Theme: input.theme,
			Genre: input.genre,
			Style: input.style,
			Keywords: input.keywords,
			Year: input.year === void 0 || input.year === null ? void 0 : String(input.year).trim(),
			Melody: input.melody,
			Attachments: input.attachments,
			"Strumming Patterns": input.strummingPatterns?.map((pattern) => typeof pattern === "string" ? { pattern } : pattern)
		},
		sections
	};
	return withValidation(songObjectToMarkdown(song, { preamble: input.preamble ?? `# ${song.config.Title}` }), {});
}
/** Serialize a song object (`schema.md` §8.2) and validate the notation. */
function songFromObject(song, { preamble = "" } = {}) {
	return withValidation(songObjectToMarkdown(song, { preamble }), {});
}
/**
* Convert a plain chord sheet — title and metadata lines, `[Verse]`-style
* labels, chord lines over lyric lines — into Open Lyric notation, the way the
* editor's paste import does.
*/
function importPlainText(rawText) {
	const result = parseOpenLyricPlainText(String(rawText ?? ""));
	return withValidation(`${String(result.markdown ?? "").trim()}\n`, {
		matchesPlainTextFormat: Boolean(result.matchesPlainTextFormat),
		renamedSections: Array.isArray(result.renamedSections) ? result.renamedSections.map((entry) => ({
			from: String(entry.from ?? ""),
			to: String(entry.to ?? "")
		})) : [],
		placeholdersUsed: Boolean(Array.isArray(result.placeholdersUsed) ? result.placeholdersUsed.length : result.placeholdersUsed),
		hasConflictingDuplicates: Boolean(result.hasConflictingDuplicates)
	});
}
var CONFIG_ENTRY_RE = new RegExp(`^\\s*-\\s*(${CONFIG_FIELD_MATCH_NAMES$1.map(escapeRegex).join("|")})\\s*:`);
var ANY_CONFIG_ENTRY_RE = /^\s*-\s*[^:]+:/;
var MULTILINE_FIELD_NAMES = new Set(CONFIG_MULTILINE_FIELD_NAMES$1);
function requireConfigFence(text) {
	const configFence = parseOpenLyricFences(text).find((fence) => fence.parsedHeader?.header === "Config");
	if (!configFence) throw new SongOperationError("The document has no ol:Config fence — create the song first (create_song).");
	return configFence;
}
function canonicalFieldName(field) {
	const name = normalizeConfigFieldName(field);
	const match = CONFIG_FIELD_NAMES$1.find((candidate) => candidate.toLowerCase() === name.toLowerCase());
	if (!match) throw new SongOperationError(`"${field}" is not a Config field. Use one of: ${CONFIG_FIELD_NAMES$1.join(", ")}.`);
	return match;
}
function isEmptyValue(value) {
	if (value === void 0 || value === null) return true;
	if (Array.isArray(value)) return value.length === 0;
	return typeof value === "string" && !value.trim();
}
/**
* Set, replace or (with an empty value) remove one Config field. A field the
* fence does not declare yet is inserted at its canonical position. The
* multiline fields take a list (one entry per line; `Strumming Patterns`
* entries may be `{ label, pattern }`).
*/
function setConfigField(text, field, value) {
	const source = normalizeNewlines$3(text);
	const name = canonicalFieldName(field);
	const configFence = requireConfigFence(source);
	const lines = splitLines(source);
	const bodyStart = configFence.startLineNumber + 1;
	const bodyEnd = configFence.endLineNumber - 1;
	let entryLine = 0;
	let entryEnd = 0;
	for (let lineNumber = bodyStart; lineNumber <= bodyEnd; lineNumber += 1) {
		const match = lines[lineNumber - 1].match(CONFIG_ENTRY_RE);
		if (match && normalizeConfigFieldName(match[1]) === name) {
			entryLine = lineNumber;
			entryEnd = lineNumber;
			if (MULTILINE_FIELD_NAMES.has(name)) for (let next = lineNumber + 1; next <= bodyEnd; next += 1) {
				const nextLine = lines[next - 1];
				if (ANY_CONFIG_ENTRY_RE.test(nextLine) && !/^[ \t]/.test(nextLine)) break;
				if (nextLine.trim()) entryEnd = next;
			}
			break;
		}
	}
	const nextLines = isEmptyValue(value) ? [] : formatConfigFieldLines(name, MULTILINE_FIELD_NAMES.has(name) && typeof value === "string" ? splitLines(value) : value);
	if (!nextLines.length && CONFIG_REQUIRED_FIELD_NAMES$1.includes(name)) throw new SongOperationError(`${name} is required and cannot be removed.`);
	if (entryLine) {
		const nextText = replaceTextLineRange(source, entryLine, entryEnd, nextLines) ?? source;
		return withValidation(nextText, {
			field: name,
			action: nextText === source ? "unchanged" : nextLines.length ? "set" : "removed"
		});
	}
	if (!nextLines.length) return withValidation(source, {
		field: name,
		action: "unchanged"
	});
	const fieldOrder = CONFIG_FIELD_NAMES$1.indexOf(name);
	let insertBefore = configFence.endLineNumber;
	for (let lineNumber = bodyStart; lineNumber <= bodyEnd; lineNumber += 1) {
		const match = lines[lineNumber - 1].match(CONFIG_ENTRY_RE);
		if (match && CONFIG_FIELD_NAMES$1.indexOf(normalizeConfigFieldName(match[1])) > fieldOrder) {
			insertBefore = lineNumber;
			break;
		}
	}
	return withValidation(replaceTextLineRange(source, insertBefore, insertBefore - 1, nextLines) ?? source, {
		field: name,
		action: "added"
	});
}
function findSectionFence(text, partName) {
	const wanted = String(partName ?? "").trim();
	const fence = parseOpenLyricFences(text).find((candidate) => candidate.parsedHeader?.header !== "Config" && candidate.parsedHeader?.partName === wanted);
	if (!fence) {
		const declared = Array.from(collectDeclaredSectionPartNames(text));
		throw new SongOperationError(`No section "${wanted}" in the song.${declared.length ? ` Sections: ${declared.join(", ")}.` : ""}`);
	}
	return fence;
}
function getSectionTypeOption(header) {
	const options = getSectionTypeOptions();
	const option = options.find((candidate) => candidate.header === header);
	if (!option) throw new SongOperationError(`"${header}" is not a section type. Use one of: ${options.map((candidate) => candidate.header).join(", ")} (spelling is exact).`);
	return option;
}
function appendStructureStep(text, token) {
	const configFence = requireConfigFence(text);
	const lines = splitLines(text);
	for (let lineNumber = configFence.startLineNumber + 1; lineNumber < configFence.endLineNumber; lineNumber += 1) {
		const match = lines[lineNumber - 1].match(/^(\s*-\s*Structure\s*:)([ \t]*)(.*?)\s*$/);
		if (!match) continue;
		const current = match[3];
		const parsed = parseStructureValue(current);
		if (parsed.error) throw new SongOperationError(`The section was added, but Structure "${current}" does not parse (${parsed.error.message}); fix it before appending.`);
		lines[lineNumber - 1] = `${match[1]} ${current}${token}`;
		return lines.join("\n");
	}
	return setConfigField(text, "Structure", token).text;
}
/**
* The index a new section gets when none is asked for: the first of its type
* is un-numbered (`Bridge`) — except a verse, conventionally `Verse 1` — and
* later ones take the next free number, an un-numbered part counting as 1
* (`Chorus` → `Chorus 2`).
*/
function pickSectionIndexText(declared, option) {
	if (!option.allowsNumbering) return "";
	const header = option.header;
	const hasPlain = declared.has(header);
	const hasNumbered = Array.from(declared).some((partName) => new RegExp(`^${escapeRegex(header)} [1-9]\\d*$`).test(partName));
	if (!hasPlain && !hasNumbered) return header === "Verse" ? "1" : "";
	return getNextFreeSectionIndexText(hasPlain ? /* @__PURE__ */ new Set([...declared, `${header} 1`]) : declared, header, option);
}
function addSection(text, { header, index, lines = [], appendToStructure = true }) {
	const source = normalizeNewlines$3(text);
	const option = getSectionTypeOption(String(header ?? "").trim());
	if (index !== void 0 && index !== null && !option.allowsNumbering) throw new SongOperationError(`${option.header} sections are not numbered.`);
	const declared = collectDeclaredSectionPartNames(source);
	const indexText = index !== void 0 && index !== null ? String(index) : pickSectionIndexText(declared, option);
	const partName = formatDeclaredPartName(option.header, indexText);
	if (declared.has(partName) && !option.allowsDuplicates) throw new SongOperationError(`${partName} already exists.`);
	const insertion = buildSectionInsertion(source, partName);
	if (!insertion) throw new SongOperationError(`Cannot add a section named "${partName}".`);
	const fenceLines = [...insertion.nextLines];
	fenceLines.splice(fenceLines.length - 1, 0, ...lines.map(String));
	let nextText = replaceTextLineRange(source, insertion.startLineNumber, insertion.endLineNumber, fenceLines) ?? source;
	if (appendToStructure) {
		const code = STRUCTURE_CODES_BY_HEADER.get(option.header);
		if (code) nextText = appendStructureStep(nextText, `${code}${indexText}`);
	}
	return withValidation(nextText, { partName });
}
function renameSection(text, from, to) {
	const source = normalizeNewlines$3(text);
	const fence = findSectionFence(source, from);
	const nextHeader = parseFenceHeader(String(to ?? "").trim());
	if (!nextHeader?.partName || nextHeader.header === "Config") throw new SongOperationError(`"${to}" is not a section name (e.g. "Verse 2", "Bridge", "Outro").`);
	if (nextHeader.partName !== fence.parsedHeader.partName && collectDeclaredSectionPartNames(source).has(nextHeader.partName) && !nextHeader.definition?.allowsDuplicateDeclaredPart?.()) throw new SongOperationError(`${nextHeader.partName} already exists.`);
	const edit = buildSectionRenameEdit(source, fence.startLineNumber, fence.parsedHeader.partName, nextHeader.partName);
	if (!edit) throw new SongOperationError(`Cannot rename ${fence.parsedHeader.partName} to ${nextHeader.partName}.`);
	return withValidation(replaceTextLineRange(source, edit.startLineNumber, edit.endLineNumber, edit.nextLines) ?? source, {
		partName: nextHeader.partName,
		structureStepsUpdated: Number(edit.structureStepCount) || 0
	});
}
function deleteSection(text, partName) {
	const source = normalizeNewlines$3(text);
	const fence = findSectionFence(source, partName);
	const edit = buildSectionDeleteEdit(source, fence.startLineNumber, fence.endLineNumber, fence.parsedHeader.partName);
	if (!edit) throw new SongOperationError(`Cannot delete ${partName}.`);
	return withValidation(replaceTextLineRange(source, edit.startLineNumber, edit.endLineNumber, edit.nextLines) ?? source, { structureStepsRemoved: Number(edit.structureStepCount) || 0 });
}
/** Replace a section's body — every line between its fences. */
function setSectionLines(text, partName, lines) {
	const source = normalizeNewlines$3(text);
	const fence = findSectionFence(source, partName);
	const bodyLines = lines.flatMap((line) => splitLines(line));
	return withValidation(replaceTextLineRange(source, fence.startLineNumber + 1, fence.endLineNumber - 1, bodyLines) ?? source, { partName: fence.parsedHeader.partName });
}
/** The section's body lines, as written. */
function getSectionLines(text, partName) {
	const source = normalizeNewlines$3(text);
	const fence = findSectionFence(source, partName);
	const lines = splitLines(source).slice(fence.startLineNumber, fence.endLineNumber - 1);
	return {
		partName: fence.parsedHeader.partName,
		header: fence.parsedHeader.header,
		lines,
		startLine: fence.startLineNumber,
		endLine: fence.endLineNumber
	};
}
/** A Khmer locale tag: `km`, `km-KH`. */
var KHMER_LOCALE_RE = /^km(?:[-_]|$)/iu;
/**
* Said when a song declares Khmer: in the editor the km-KH plugin adds a
* word-separator repair to Format that this language-neutral server has no
* plugin for.
*/
var KHMER_FORMAT_HINT = "The song's Locales include Khmer. In the editor, the km-KH plugin's Format also turns a space typed between Khmer letters into a zero-width word break (U+200B); no language plugin runs here, so that was not done. khmer-lint's fix_khmer with rules ['word-separator'] makes the same repair — but a visible space between Khmer phrases is also how a phrase ends, so review it before applying.";
/**
* The editor's Format Document as it runs with no language plugin: per line,
* repeated invisible characters collapsed and trailing whitespace removed.
* (The word-separator repair a language plugin registers — Khmer's, from the
* km-KH plugin — has no plugin to come from here; `hint` says so when the song
* declares Khmer.)
*/
function formatSong(text) {
	const source = normalizeNewlines$3(text);
	const nextText = splitLines(source).map((line) => formatDocumentLineWhitespace(line)).join("\n");
	const declaresKhmer = (songObjectFromMarkdown(source).song.config.Locales ?? []).some((locale) => KHMER_LOCALE_RE.test(String(locale).trim()));
	return withValidation(nextText, {
		changedLines: countChangedLines(source, nextText),
		...declaresKhmer ? { hint: KHMER_FORMAT_HINT } : {}
	});
}
/** Passes {@link applyFixes} makes at most: a fix can reveal another. */
var APPLY_FIXES_MAX_PASSES = 10;
/** The UTF-16 offset of a 1-based `line`/`column` in `lineStarts`' text. */
function offsetOf(lineStarts, textLength, line, column) {
	const start = lineStarts[Math.max(0, line - 1)] ?? textLength;
	return Math.min(textLength, start + Math.max(0, column - 1));
}
/**
* Apply every fix the validator knows — the `fix` each diagnostic of
* {@link validateSong} may carry, the quick fixes the editor offers one at a
* time — and validate again, until no diagnostic has one left (a corrected
* fence header can let the next check through). Fixes whose ranges overlap
* wait for the next pass. `applied` lists what was done; the diagnostics with
* no known fix stay in `validation` for the caller to resolve.
*/
function applyFixes(text) {
	let current = normalizeNewlines$3(text);
	const applied = [];
	for (let pass = 0; pass < APPLY_FIXES_MAX_PASSES; pass += 1) {
		const fixable = validateSong(current).diagnostics.filter((diagnostic) => diagnostic.fix);
		if (!fixable.length) break;
		const lineStarts = [0];
		for (let index = 0; index < current.length; index += 1) if (current[index] === "\n") lineStarts.push(index + 1);
		const ranges = fixable.map((diagnostic) => ({
			diagnostic,
			start: offsetOf(lineStarts, current.length, diagnostic.line, diagnostic.column),
			end: offsetOf(lineStarts, current.length, diagnostic.endLine, diagnostic.endColumn)
		})).sort((a, b) => b.start - a.start || b.end - a.end);
		let next = current;
		let boundary = Infinity;
		const passApplied = [];
		for (const { diagnostic, start, end } of ranges) {
			if (end > boundary || end < start) continue;
			next = `${next.slice(0, start)}${diagnostic.fix.text}${next.slice(end)}`;
			boundary = start;
			passApplied.unshift({
				message: diagnostic.message,
				title: diagnostic.fix.title,
				line: diagnostic.line,
				column: diagnostic.column
			});
		}
		if (next === current) break;
		current = next;
		applied.push(...passApplied);
	}
	return withValidation(current, { applied });
}
//#endregion
//#region src/open-lyric-mcp/context.ts
/** Extensions a song file may be written back to. */
var SONG_FILE_EXTENSIONS = [".md", ".markdown"];
async function readSongSource(files, { text, path }) {
	if (typeof text === "string" && path) throw new SongOperationError("Pass the song as text or as a path, not both.");
	if (typeof text === "string") return { text };
	if (path) {
		const file = await files.readText(path);
		return {
			text: file.text,
			path: file.path
		};
	}
	throw new SongOperationError("Pass the song as text, or a path to a song file.");
}
/**
* Finish an edit tool: for text input, return the new text; for a file, write
* it back (unless `dryRun`, or the server is read-only — then return the text
* and say why it was not written).
*/
async function finishSongEdit(files, source, result, { dryRun = false, summary }) {
	const { text, ...rest } = result;
	const status = summarizeValidation(result.validation);
	if (!source.path) return structuredResult({
		...rest,
		text,
		written: false
	}, `${summary}\n${status}`);
	if (dryRun || files.readOnly) {
		const note = dryRun ? "Dry run: the file was not written." : "The server is read-only: the file was not written.";
		return structuredResult({
			...rest,
			text,
			path: source.path,
			written: false,
			note
		}, `${summary}\n${note}\n${status}`);
	}
	if (text === source.text) return structuredResult({
		...rest,
		path: source.path,
		written: false,
		note: "No change."
	}, `${summary}\nNo change; the file was left alone.\n${status}`);
	await files.writeFile(source.path, text, SONG_FILE_EXTENSIONS);
	return structuredResult({
		...rest,
		path: source.path,
		written: true
	}, `${summary}\nWrote ${source.path}.\n${status}`);
}
/** A new song from a create-style tool: return it, or write it to `path`. */
async function finishNewSong(files, result, { path, overwrite = false, summary }) {
	const { text, ...rest } = result;
	const status = summarizeValidation(result.validation);
	if (!path) return structuredResult({
		...rest,
		text,
		written: false
	}, `${summary}\n${status}`);
	const target = await files.resolveForWrite(path, SONG_FILE_EXTENSIONS);
	if (!overwrite) try {
		await files.resolveForRead(target);
		throw new SongOperationError(`${target} already exists — pass overwrite: true to replace it.`);
	} catch (error) {
		if (error instanceof SongOperationError) throw error;
	}
	const written = await files.writeFile(target, text, SONG_FILE_EXTENSIONS);
	return structuredResult({
		...rest,
		path: written.path,
		written: true
	}, `${summary}\nWrote ${written.path}.\n${status}`);
}
//#endregion
//#region src/open-lyric-mcp/prompts.ts
/**
* Prompt templates for the common song jobs. Each tells the model which tools
* to use and to validate at the end; the ones about an existing song inline
* it (from `text`, or read from `path`) together with its current diagnostics.
*/
function userMessage(text) {
	return { messages: [{
		role: "user",
		content: {
			type: "text",
			text
		}
	}] };
}
async function describeSongArgument(files, { text, path }) {
	let songText = text ?? "";
	let origin = "the song below";
	if (!songText && path) try {
		songText = (await files.readText(path)).text;
		origin = `the song in ${path} (shown below; edit the file with the path-based tools)`;
	} catch (error) {
		return `The song should be read from ${path}, but reading it failed: ${errorMessage(error)}. Use read_song once the path is right.`;
	}
	if (!songText) return "No song was given: ask for it, or use list_songs and read_song to find it.";
	const validation = validateSong(songText);
	return [
		`Work on ${origin}.`,
		"",
		"```markdown",
		songText,
		"```",
		"",
		`Current validation: ${summarizeValidation(validation)}`
	].join("\n");
}
var NOTATION_HINT = "Open Lyric is Markdown with ```ol:<Section> fences: one ol:Config fence (Title, Structure, Key …) and one fence per section (Verse 1, Chorus, Bridge …), with chords as [G] annotations placed before the syllable they land on. Read open-lyric://docs/notation (or get_notation_reference) for the rules.";
var songArgs = {
	text: z.string().optional().describe("The song notation."),
	path: z.string().optional().describe("Or a song file inside the allowed roots.")
};
function registerOpenLyricPrompts(server, files) {
	server.registerPrompt("write_song", {
		title: "Write a new song",
		description: "Write an original song in Open Lyric notation.",
		argsSchema: {
			topic: z.string().describe("What the song is about."),
			key: z.string().optional().describe("e.g. G or Em."),
			style: z.string().optional().describe("Genre, feel or tempo."),
			language: z.string().optional().describe("Lyric language, e.g. en-US.")
		}
	}, ({ topic, key, style, language }) => userMessage([
		`Write an original song about: ${topic}.`,
		key ? `Key: ${key}.` : "",
		style ? `Style: ${style}.` : "",
		language ? `Lyrics in ${language} (set Locales accordingly).` : "",
		"",
		NOTATION_HINT,
		"Build it with create_song (sections with [Chord] annotations, a Structure that repeats the chorus), then run validate_song and fix every error before showing the result."
	].filter(Boolean).join("\n")));
	server.registerPrompt("convert_chord_sheet", {
		title: "Convert a chord sheet",
		description: "Turn a pasted chord sheet (chords over lyrics, ChordPro …) into Open Lyric.",
		argsSchema: { chordSheet: z.string().describe("The chord sheet text.") }
	}, ({ chordSheet }) => userMessage([
		"Convert this chord sheet to Open Lyric notation.",
		"",
		"```text",
		chordSheet,
		"```",
		"",
		NOTATION_HINT,
		"First try import_plain_text; if it does not match the plain-text layout, write the song with create_song: move each chord from the chord line onto the lyric syllable under it as [Chord], map section labels to Open Lyric sections, and derive Structure from the order the sections are sung. Keep chord spellings. Finish with validate_song and fix every error."
	].join("\n")));
	server.registerPrompt("fix_song", {
		title: "Fix validation errors",
		description: "Fix every diagnostic in a song without changing its content.",
		argsSchema: songArgs
	}, async (args) => userMessage([
		await describeSongArgument(files, args),
		"",
		"Fix every error and warning while keeping the lyrics, chords and order. Start with apply_fixes: it applies every diagnostic that carries a fix (a near-miss section header, a Config field name or value, a chord annotation) and validates again. For what is left, look each message up in the Diagnostics section of the notation reference (get_notation_reference section 6) when unsure, use the editing tools (set_config_field, set_section_lines, rename_section …), and run validate_song until it is clean."
	].join("\n")));
	server.registerPrompt("add_translation", {
		title: "Add a translation",
		description: "Add translation lines under each lyric line.",
		argsSchema: {
			...songArgs,
			language: z.string().describe("Target language, e.g. km-KH or fr-FR.")
		}
	}, async ({ language, ...args }) => userMessage([
		await describeSongArgument(files, args),
		"",
		`Add a ${language} translation: under each lyric line, add an indented line (a tab) with its translation, without chord annotations. Leave progression and comment lines alone. Add ${language} to Config Locales (set_config_field). Use set_section_lines per section, then validate_song.`
	].join("\n")));
	server.registerPrompt("review_song", {
		title: "Review a song",
		description: "Review notation, structure, chords and lyrics, and suggest improvements.",
		argsSchema: songArgs
	}, async (args) => userMessage([
		await describeSongArgument(files, args),
		"",
		"Review the song: notation problems (validate_song), structure (explain_structure — unused or missing sections, repeats), chords (list_chords — out-of-key chords, awkward changes), lyric flow and singability. List concrete suggestions; do not edit unless asked."
	].join("\n")));
	server.registerPrompt("arrange_song", {
		title: "Arrange a song",
		description: "Propose and apply an arrangement: intro, dynamics, repeats, tags.",
		argsSchema: {
			...songArgs,
			goal: z.string().optional().describe("e.g. \"a 4-minute live version\".")
		}
	}, async ({ goal, ...args }) => userMessage([
		await describeSongArgument(files, args),
		"",
		`Arrange the song${goal ? ` for: ${goal}` : ""}. Consider an Intro/Outro progression, an Instrumental or Interlude, a Bridge or Tag, repeat counts in Structure, {c: …} arrangement cues and strumming patterns. Explain the plan, then apply it with add_section, set_section_lines and set_config_field (Structure), and validate_song at the end.`
	].join("\n")));
}
//#endregion
//#region .claude/open-lyric/schema.md?raw
var schema_default = "# Open Lyric — notation schema\n\nThe complete grammar of the Open Lyric song notation: the fenced sections a\ndocument may contain, the `Config` metadata fence, the inline chord/bar/directive\nsyntax, the compact `Structure` codes, and every diagnostic the validator emits.\n\nEverything here is what the parser and validator actually enforce. Patterns are\nwritten as JavaScript regular-expression sources.\n\n---\n\n## 1. Document shape\n\nAn Open Lyric document is a **Markdown file**. Anything outside an `ol:` fence is\nordinary Markdown and is not validated as notation.\n\nEach song section is a fenced block whose info string starts with `ol:`:\n\n````text\n```ol:Verse 1\nMorning breaks with mercy on the water\n```\n````\n\n| Rule            | Value                                                             |\n| --------------- | ----------------------------------------------------------------- |\n| Fence open      | `^\\s*```ol:(.*)$` — the capture is the header, plus optional index |\n| Fence close     | `^\\s*```\\s*$`                                                     |\n| Header, plain   | `^<Header>$`                                                      |\n| Header, indexed | `^<Header>(?:\\s+([1-9]\\d*))?$` (only where numbering is allowed)   |\n| Comment line    | `^\\s*//` — valid in every fence                                   |\n\n- Header spelling is **case-sensitive and exact**. `ol:config` is rejected; use\n  `ol:Config`.\n- **Part name** is the fence's identity: the header, plus `\" \" + index` when\n  numbered (`Verse 2`). `Structure` and the duplicate check both work on part\n  names.\n- Each part name may be declared **once** per document.\n- `ol:Config` is **required**. Every other section is optional.\n- Comment lines are ignored by validation and shown in the preview (muted)\n  unless comments are turned off. `Config` comments always stay hidden — they\n  surface as strumming-pattern labels instead.\n\n---\n\n## 2. Sections\n\n| Header         | Kind         | Numbered | Structure code | Body rule     |\n| -------------- | ------------ | -------- | -------------- | ------------- |\n| `Config`       | config       | no       | —              | config        |\n| `Intro`        | intro        | no       | `I`            | mixed         |\n| `Verse`        | lyric        | yes      | `V`            | lyric         |\n| `Pre-Chorus`   | lyric        | yes      | `P`            | lyric         |\n| `Chorus`       | lyric        | yes      | `C`            | lyric         |\n| `Post-Chorus`  | lyric        | yes      | `X`            | lyric         |\n| `Final-Chorus` | lyric        | no       | `F`            | lyric         |\n| `Bridge`       | lyric        | yes      | `B`            | lyric         |\n| `Refrain`      | lyric        | yes      | `R`            | lyric         |\n| `Tag`          | lyric        | yes      | `T`            | lyric         |\n| `Note`         | lyric        | yes      | `N`            | lyric         |\n| `Instrumental` | instrumental | yes      | `IS`           | progression   |\n| `Interlude`    | instrumental | yes      | `L`            | progression   |\n| `Turnaround`   | turnaround   | yes      | `TU`           | mixed         |\n| `Outro`        | outro        | no       | `O`            | mixed         |\n| `Breakdown`    | freeText     | yes      | `D`            | free text     |\n| `Vamp`         | freeText     | no       | `A`            | free text     |\n| `Solo`         | freeText     | yes      | `S`            | free text     |\n\n### Body rules\n\n**`lyric`** — free lyric text. Only two things are checked: every `[` must open a\nvalid chord annotation and close on the same line, and a bare `]` is an error.\nLeading and interior `|` bar markers are allowed for bar-aligned lyrics. An\nindented line under a lyric line reads as its **translation line**.\n\n**`progression`** (`Instrumental`, `Interlude`) — the whole body is joined into\none chord progression. It may open with a single `{c: …}` cue directive;\neverything after that must be bar tokens, chord symbols and `(Nx)` repeat\nsuffixes. No lyric text.\n\n**`mixed`** (`Intro`, `Outro`, `Turnaround`) — each line is classified on its own.\nA line reads as a **progression** when it contains a `|` *and* at least one\nwhole-token chord symbol, or when it starts with `{p:` / `{c:`. Every other line\nreads as a **lyric** line. This is what lets a sung intro sit under the\nprogression that sets it up.\n\n> Caution: a lyric line that uses `|` separators *and* contains a standalone\n> chord-looking word (`| Hello | D |`) is classified as a progression, and its\n> words are then flagged as invalid tokens. Attach chords as `[D]` annotations\n> instead.\n\n**`free text`** (`Breakdown`, `Vamp`, `Solo`) — not validated. Spoken cues,\nad-lib directions, arrangement notes: anything.\n\n---\n\n## 3. Inline notation\n\n### Chord symbol\n\n```text\n[A-G](?:#|b)?(?:(?:maj|min|m|dim|aug)(?:2|4|5|6|7|9|11|13)?|sus(?:2|4)?|(?:add|no|omit)(?:2|4|5|6|7|9|11|13)|(?:2|4|5|6|7|9|11|13))?(?:\\/[A-G](?:#|b)?)?\n```\n\n- **Root** — `A`–`G`, with an optional `#` or `b`.\n- **Decoration** — at most **one** of: a quality (`maj`, `min`, `m`, `dim`, `aug`)\n  with an optional extension; `sus` / `sus2` / `sus4`; `add`/`no`/`omit` +\n  extension; or a bare extension.\n- **Extensions** — `2 4 5 6 7 9 11 13`.\n- **Slash bass** — optional `/<root>`, e.g. `D/F#`.\n\nValid: `C` `Am` `Bm7` `Em7` `Cadd9` `Gsus4` `Cmaj7` `D/F#` `F#m` `Bb` `Ebm` `A/C#`\n\nInvalid: `C7sus4` (two decorations) · `Cm7b5` (no altered fifth) · `H` (root must\nbe `A`–`G`) · `Gadd` (`add`/`no`/`omit` need an extension)\n\n### Chord annotation\n\n`^\\[<chordSymbol>\\]$` — placed inline, immediately before the syllable the chord\nlands on:\n\n```text\n[D]You turn the darkest night to [A/C#]morning\n```\n\n### Bar tokens\n\n`||:` `|:` `:||` `:|` `|`\n\n### Repeat suffix\n\n`^\\([1-9]\\d*x\\)` — `(2x)`, `(4x)`, `(12x)`.\n\nRejected: `(02x)` `( 2x)` `(2x )` `(x2)` `(2X)`.\n\nProgression lines only (`Instrumental`, `Interlude`, and progression lines inside\n`Intro`/`Outro`/`Turnaround`). Inside a `Structure` value the compact form `x2` is\nused instead — note the reversed order.\n\n### Directives\n\nA directive must be the **first token** of its line (mixed sections) or of the\nbody (`Instrumental` / `Interlude`).\n\n| Directive          | Pattern                            | Example             | Allowed in                                                     |\n| ------------------ | ---------------------------------- | ------------------- | -------------------------------------------------------------- |\n| Strumming pattern  | `^\\{p:\\s*#[1-9]\\d*\\s*\\}`           | `{p: #2}`           | `Intro`, `Outro`, `Turnaround`                                  |\n| Arrangement cue    | `^\\{c:\\s*[A-Za-z0-9 +\\-\\/#]+\\s*\\}` | `{c: Piano + Pads }` | `Intro`, `Outro`, `Turnaround`, `Instrumental`, `Interlude`     |\n\n`{p: #N}` selects the Nth pattern from the `Config` `Strumming Patterns` list\n(1-based, in listed order). `{c: …}` accepts letters, digits, space, `+`, `-`,\n`/` and `#` only.\n\n### Markdown inside fences\n\n`**bold**`, `*italic*` and `<font color=\"#0f766e\">colored</font>` render inside\nfence bodies and do not interfere with chord alignment.\n\n### Translation lines\n\nAn indented line directly under a lyric line renders paired with it, and may omit\nchord annotations:\n\n```text\n|[Bm7]Holy are You Lord |[G]Faithful are You Lord\n	Holy are You Lord  Faithful are You Lord\n```\n\n---\n\n## 4. The `Config` fence\n\nField lines take the form `- Field: value`. Indented continuation lines are\nallowed **only** under `Description`, `Attachments` and `Strumming Patterns`.\n\n| Field                | Required | Notes                                                     |\n| -------------------- | -------- | --------------------------------------------------------- |\n| `Title`              | **yes**  |                                                           |\n| `Subtitle`           | no       |                                                           |\n| `Description`        | no       | multiline                                                 |\n| `Artist`             | no       |                                                           |\n| `Copyright`          | no       |                                                           |\n| `Locales`            | no       | comma-separated, from the closed tag set                  |\n| `Key`                | no       | enum                                                      |\n| `Tempo`              | no       | `^[1-9]\\d*bpm$` — no space, e.g. `68bpm`                  |\n| `Time`               | no       | enum                                                      |\n| `Theme`              | no       |                                                           |\n| `Structure`          | **yes**  | see §5                                                    |\n| `Genre`              | no       |                                                           |\n| `Style`              | no       |                                                           |\n| `Keywords`           | no       | comma-separated free text                                 |\n| `Year`               | no       | `^[1-9]\\d{3}$` — four digits, e.g. `2024`                 |\n| `Melody`             | no       | free text — the tune the lyrics are sung to               |\n| `Attachments`        | no       | multiline, one URL per line                               |\n| `Strumming Patterns` | no       | multiline; alias `Strumming Pattern` is accepted          |\n\n**`Key`** — `C Db D Eb E F F# Gb G Ab A Bb B Am Bbm Bm Cm C#m Dm D#m Ebm Em Fm F#m Gm G#m`\n\n**`Time`** — `4/4 2/2 2/4 3/4 3/8 6/8 9/8 12/8`\n\n**`Locales`** — comma-separated tags from a **closed set** (the Windows LCID tag\nlist, 229 entries: `en-US`, `km-KH`, `fr-FR`, `zh-CN`, …), written as listed:\n`en-us` is an error whose message names the listed `en-US`, and whose quick\nfix writes it (§6). Duplicates and\nempty entries are errors too. The complete list is enumerated in the grammar\nJSON of §8, under `config.locales.values`.\n\n**`Keywords`** — free-text search terms on one line, separated by commas:\n`- Keywords: grace, morning, worship`. Any script is fine; nothing is checked\nbeyond the value being present. The song object (§8.2) carries them as a list.\n\n**`Year`** — the year the song was written or released, as four ASCII digits\n(`2024`). A two-digit year, a range (`2023-2024`) or other-script digits are\nreported.\n\n**`Melody`** — the tune the lyrics are sung to, typically the name of an\nexisting melody (`- Melody: Amazing Grace`). Free text, like `Genre`.\n\n**`Attachments`** — one per line, either a bare URL or a Markdown link:\n\n```text\n- Attachments: https://example.com/audio/demo.mp3\n	[Piano Chart](file:///C:/Charts/song.pdf)\n```\n\nPattern: `^(?:(?:[A-Za-z][A-Za-z0-9+.-]*:\\/\\/\\S[^\\r\\n]*)|\\[[^\\]\\r\\n]+\\]\\((?:[A-Za-z][A-Za-z0-9+.-]*:\\/\\/\\S[^\\r\\n)]*)\\))$`.\nDetected types: `youtube`, `audio`, `video`, `pdf`, `image`, `other`.\n\n**`Strumming Patterns`** — one pattern per indented line. Step characters:\n`d D v V u U ^ x X 1 * + - _ . 0`; separators `|`, space and tab. A `//` comment\nline above a pattern becomes its label in the preview. Patterns are numbered from\n1 in listed order and referenced by `{p: #N}`.\n\n```text\n- Strumming Patterns:\n	// Slow rolling pulse\n	d--u-- | d-u---\n```\n\n---\n\n## 5. `Structure`\n\nThe performance order of the song, written as one compact token string —\nno whitespace, no separators.\n\n```text\n- Structure: IV1x2CV1V2CO\n```\n\n| Code | Section        | Numbered | Code | Section      | Numbered |\n| ---- | -------------- | -------- | ---- | ------------ | -------- |\n| `I`  | Intro          | no       | `IS` | Instrumental | yes      |\n| `V`  | Verse          | yes      | `L`  | Interlude    | yes      |\n| `P`  | Pre-Chorus     | yes      | `D`  | Breakdown    | yes      |\n| `C`  | Chorus         | yes      | `R`  | Refrain      | yes      |\n| `X`  | Post-Chorus    | yes      | `T`  | Tag          | yes      |\n| `F`  | Final-Chorus   | no       | `TU` | Turnaround   | yes      |\n| `B`  | Bridge         | yes      | `A`  | Vamp         | no       |\n| `N`  | Note           | yes      | `S`  | Solo         | yes      |\n| `O`  | Outro          | no       |      |              |          |\n\n- Codes are matched **longest-first**, so `IS` reads as Instrumental, never as\n  Intro + Solo.\n- **Index** — `[1-9]\\d*` immediately after the code (`V1`), and only for a\n  section that allows numbering.\n- **Repeat** — `x[1-9]\\d*` after the code and index (`V1x2` = play Verse 1\n  twice).\n- Every token must name a part the document actually **declares as a fence**.\n- The same part may not appear **twice in a row** — raise the previous token's\n  repeat count instead (`Cx2`, not `CC`).\n- A declared section the Structure never names is valid, with no diagnostic.\n  The preview leaves it out of the song, with one exception: a `Note`.\n\n### Notes in the Structure, or after it\n\nA `Note` fence can be shown in two places:\n\n- **In the flow.** Name it in the Structure (`IV1CN1V2CO`). It is a step of\n  the song like any section: it renders in that place with its flow index, and\n  it takes that place in the plain text and in a slide deck.\n- **After the song.** Leave it out of the Structure. The preview then lists it\n  below the song's sections, in the order the notes are written, with no flow\n  index. It follows the song in the plain text too, and in a slide deck it can\n  close the deck. The preview's **Show song notes** setting (on by default)\n  and the render option `hideNotes` leave such notes out.\n\nA note named in the Structure never also appears after the song, so it\nshows once either way.\n\n---\n\n## 6. Diagnostics\n\nEvery message the validator can emit, and what triggers it.\n\nA diagnostic that names its fix also carries it as data: `fix: { title,\ntext }`, meaning *put `text` in place of the diagnostic's range*. The\neditor and VS Code offer it as a preferred quick fix (the light bulb,\n`Ctrl+.` / `Cmd+.`), withdrawn once the text under it changes; while two or\nmore apply, the light bulb also offers **Fix all N Open Lyric problems**, and\na `source.fixAll` request (Fix All, a save action) gets that edit as\n`source.fixAll.openLyric`. The MCP's `validate_song` returns the fix with each\ndiagnostic, and its `apply_fixes` applies them all. These carry one:\n\n| Diagnostic | Range | `text` | `title` |\n| --- | --- | --- | --- |\n| `Unsupported ol part. Did you mean ol:<Header>?` | the header after `ol:` | `<Header>` | `Change to ol:<Header>` |\n| `Use ol:Config. Lowercase ol:config is not supported.` | `config` | `Config` | `Change to ol:Config` |\n| `Unsupported config field. Did you mean <Field>?` | the field name | `<Field>` — `title` → `Title`, `Strucure` → `Structure` | `Change to <Field>` |\n| `Invalid chord annotation. Try [<chord>].` | the bracketed token | `[<chord>]` | `Change to [<chord>]` |\n| `Invalid <section> token \"<token>\". Try <chord>.` | the token | `<chord>` | `Change to <chord>` |\n| `Repeat suffix must use exact format (2x).` | the parenthesised token | `(<n>x)` — `(2 X)` → `(2x)` | `Change to (<n>x)` |\n| `Key must be one of: …` | from the field's `:` to the end of the line | `: <key>` — `g` → `G`, `f♯m` → `F#m`, `E♭` → `Eb` | `Change to <key>` |\n| `Time must be one of: …` | from the field's `:` to the end of the line | `: <time>` — `4 / 4` → `4/4` | `Change to <time>` |\n| `Tempo must be a whole number of beats per minute then bpm, such as 76bpm.` | from the field's `:` to the end of the line | `: <n>bpm` — `70 bpm`, `70`, `70BPM` → `70bpm` | `Change to <n>bpm` |\n| `Unsupported locale. Use <tag> instead of <typed>.` | the tag | `<tag>` — `km-kh` → `km-KH` | `Change to <tag>` |\n\nA repeat whose count is itself wrong (`(0x)`, `(02x)`) gets no fix, and\nneither does a value with more than one reading: a Key ending in a capital\n`M` (`GM` may mean G major or G minor), a Key or Time outside its list\nhowever it is spelled, a Tempo of `0bpm` or with a fraction, a two-digit\nYear, a tag outside the locale list.\n\n### Fences\n\n| Message                                                                                                                   | Cause                                                  |\n| ------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------ |\n| `Use ol:Config. Lowercase ol:config is not supported.`                                                                     | The header spelled in lowercase.                       |\n| `Config fences cannot be numbered or suffixed.`                                                                            | `ol:Config 1` or similar.                              |\n| `<Header> fences cannot be numbered.`                                                                                      | An index on Intro, Outro, Vamp, Final-Chorus or Config. |\n| `Section indexes must start at 1.`                                                                                         | A zero or zero-padded index, e.g. `ol:Verse 01`.       |\n| `Unsupported ol part. Use Config, Intro, Instrumental, Interlude, Turnaround, lyric sections, Breakdown, Vamp, or Solo.`    | An unknown fence header.                               |\n| `Unsupported ol part. Did you mean ol:<Header>?`                                                                           | An unknown header close to a known one: a letter or two off (one for a header of four letters or fewer), or a difference of case, spaces or hyphens only — `ol:Vers 2` → `ol:Verse 2`, `ol:pre chorus 1` → `ol:Pre-Chorus 1`. |\n| `Duplicate ol part. <partName> is already declared on line N.`                                                             | The same part name declared twice.                     |\n| `Unclosed ol fence.`                                                                                                       | A missing closing ``` line.                            |\n| `Missing required ol part. Add ol:Config.`                                                                                 | No Config fence in the document.                       |\n\n### Config\n\n| Message                                                                                                                                        | Cause                                                  |\n| ---------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------ |\n| `Invalid config entry. Use - Field: value.`                                                                                                     | A `-` line with no `Field:`, such as `- Genre`.        |\n| `Unsupported config field. Use …`                                                                                                               | A `- Field: value` entry whose field is not one of §4's and not close to one, such as `- Colour: red`. The message lists them all. |\n| `Unsupported config field. Did you mean <Field>?`                                                                                               | An unknown field close to a known one: a letter or two off (one for a name of four letters or fewer), or a difference of case, spaces or hyphens only — `- title:` → `Title`, `- Strucure:` → `Structure`, `- Kye:` → `Key`. Never a field the Config already declares (above or below) or one an earlier misspelt name was pointed at, so applying every fix never makes a duplicate; with no other close field, the message lists every field instead. A misspelt `Title` or `Structure` also leaves `Missing required config fields: …` until it is fixed. |\n| `Config continuation lines must follow a Description, Attachments, or Strumming Patterns entry.`                                                 | A line that is not a `- Field:` entry, indented or not, after a single-line field. |\n| `Duplicate config field. <Field> is already declared on line N.`                                                                                | A Config field written twice.                          |\n| `<Field> must provide a value on the same line.`                                                                                                | A single-line field left empty, value on the next line. |\n| `<Field> must be one of: …`                                                                                                                     | A `Key` or `Time` value outside its enum.              |\n| `Tempo must be a whole number of beats per minute then bpm, such as 76bpm.`                                                                     | `70 bpm`, `70`, or `0bpm`.                             |\n| `Year must be a four-digit year, such as 2024.`                                                                                                 | `24`, `2023-2024`, or other-script digits.             |\n| `Missing required config fields: …`                                                                                                             | `Title` or `Structure` is absent.            |\n| `Locales must be a comma-separated list of locales with no empty entry.`                                                                        | A trailing comma or an empty slot.                     |\n| `Duplicate locale. <tag> is already listed.`                                                                                                    | The same locale tag listed twice.                      |\n| `Unsupported locale. Use <tag> instead of <typed>.`                                                                                             | A listed tag in another case, such as `en-us`.         |\n| `Unsupported locale. <typed> is not a supported locale such as en-US or km-KH.`                                                                 | A tag outside the closed set.                          |\n| `Attachments must use a protocol-based URL such as http://, https://, file:///, ftp://, ftps://, or a Markdown link whose target is such a URL. Spaces inside the URL are allowed.` | An `Attachments` value that is neither a `scheme://` URL nor a Markdown link to one, such as `demo.mp3`. |\n| `Attachments continuation lines must start with spaces or tabs and contain a protocol-based URL such as http://, https://, file:///, ftp://, ftps://, or a Markdown link that points to one. Spaces inside the URL are allowed.` | A line under `Attachments` that is not indented, or holds no such URL. |\n| `Strumming Patterns must use only d, D, v, V, u, U, ^, x, X, 1, *, +, -, _, ., 0, bar separators (\\|), and spaces or tabs.`                      | Any other character inside a pattern.                  |\n| `Strumming Patterns continuation lines must start with spaces or tabs and use only d, D, v, V, u, U, ^, x, X, 1, *, +, -, _, ., 0, bar separators (\\|), and spaces or tabs.` | A line under `Strumming Patterns` that is not indented, or holds any other character. |\n\n### Structure\n\n| Message                                                                                              | Cause                                     |\n| ---------------------------------------------------------------------------------------------------- | ----------------------------------------- |\n| `Structure must use compact codes like IV1x2CV1V2CO.`                                                 | Whitespace inside the value.              |\n| `Unknown structure code. Use …`                                                                       | A letter that is not a structure code.    |\n| `<Header> cannot be numbered in Structure.`                                                           | An index on an unnumbered section's code. |\n| `Repeat suffix must use compact format x2.`                                                           | `x` written without a count.              |\n| `Repeat counts must start at 1.`                                                                      | `x0` or `x02`.                            |\n| `Structure cannot place <part> twice in a row. Increase the previous token's repeat count instead.`    | `CC` instead of `Cx2`.                    |\n| `Structure references undeclared ol part. <part> is not declared.`                                    | A token with no matching fence. Every such token is marked, each at its own place. |\n\n### Section bodies\n\n| Message                                                             | Cause                                                                          |\n| ------------------------------------------------------------------- | ------------------------------------------------------------------------------ |\n| `Unclosed chord annotation.`                                         | A `[` with no `]` on the same line.                                            |\n| `Invalid chord annotation.`                                          | A bracketed token that is not a chord symbol and is not close to one, such as `[Hmm]`. |\n| `Invalid chord annotation. Try [<chord>].`                           | A bracketed token close to a chord symbol; the suggestion is that chord.       |\n| `Unexpected closing bracket in lyric line.`                          | A `]` with no opening `[`.                                                     |\n| `Invalid <section> token \"<token>\". Try <chord>.`                    | A progression word that is nearly a chord: bracketed (`[G]` → `G`), lowercase (`em` → `Em`), or German B (`Hm` → `Bm`). |\n| `Invalid <section> token \"<token>\". Use chords, \\| bars and (2x) repeats.` | Any other word in a progression that is neither a chord, a bar token, nor a repeat. |\n| `Invalid <section> directive. Expected {c: Piano + Pads }.`          | A malformed `{ … }` opening an Instrumental / Interlude body.                  |\n| `Invalid <section> directive. Expected {p: #3} or {c: Piano + Pads }.` | A malformed directive on a mixed-section progression line.                    |\n| `Repeat suffix must use exact format (2x).`                          | A repeat-looking token such as `(2 x)` or `(2X)`.                              |\n| `Unclosed repeat suffix.`                                            | A `(` with no `)` in a progression.                                            |\n\n---\n\n## 7. Complete example\n\n````text\n```ol:Config\n- Title: Quiet River at Dawn\n- Subtitle: A Soft 4/4 Prayer\n- Description:\n	A gentle worship draft for acoustic teams.\n- Artist: Open Lyric Team\n- Copyright: 2026 Open Lyric\n- Locales: en-US\n- Key: G\n- Tempo: 68bpm\n- Time: 4/4\n- Theme: Quiet trust\n- Structure: IV1PCXV2CO\n- Genre: Worship\n- Style: Acoustic\n- Keywords: trust, morning, worship\n- Year: 2026\n- Melody: Original tune\n- Attachments: https://example.com/audio/quiet-river-demo.mp3\n- Strumming Patterns:\n	// Slow rolling pulse\n	d--u-- | d-u---\n```\n\n```ol:Intro\n// Count the band in on bar 2\n{p: #1} | G | D/F# | Em7 | Cadd9 | (2x)\n```\n\n```ol:Verse 1\nMorning breaks with mercy on the water\nEvery breath reminds me You are near\n```\n\n```ol:Pre-Chorus\n[Em7]When the waters rise, [D]You remain\n[Cadd9]Steady as the promise [D]of Your name\n```\n\n```ol:Chorus\n|[G]Carry me gently, carry me kindly\n|[D/F#]Hold me in peace when the night feels long\n```\n\n```ol:Post-Chorus\n|[Em7]River of peace, keep carrying me\n```\n\n```ol:Verse 2\nEvery hidden worry meets Your silence\n```\n\n```ol:Outro\nStill You are near, still You are near\n```\n````\n\n---\n\n## 8. Machine-readable schema\n\nTwo JSON documents. The **grammar** describes the notation itself — every fence,\npattern, enum and diagnostic, as data. The **song schema** is a strict JSON\nSchema (draft 2020-12) for a song held as a structured object, for generating or\nvalidating a song before serializing it to notation.\n\n### 8.1 Grammar\n\n````json\n{\n  \"name\": \"open-lyric-notation\",\n  \"title\": \"Open Lyric notation grammar\",\n  \"summary\": \"Every fence, pattern, enum and diagnostic of the Open Lyric notation, as data. Regex values are JavaScript regular-expression sources.\",\n  \"document\": {\n    \"fileForm\": \"A Markdown document. Anything outside an ol: fence is ordinary Markdown and is not validated as notation.\",\n    \"fenceOpen\": {\n      \"pattern\": \"^\\\\s*```ol:(.*)$\",\n      \"note\": \"The capture is the fence info: a header, optionally followed by a space and a 1-based index.\"\n    },\n    \"fenceClose\": { \"pattern\": \"^\\\\s*```\\\\s*$\" },\n    \"headerInfo\": {\n      \"unnumbered\": \"^<Header>$\",\n      \"numbered\": \"^<Header>(?:\\\\s+([1-9]\\\\d*))?$\",\n      \"note\": \"Header spelling is case-sensitive and exact. ol:config is rejected; use ol:Config.\"\n    },\n    \"partName\": \"The fence identity used by Structure and by duplicate checks: the header, plus ' ' + index when numbered (e.g. 'Verse 2').\",\n    \"commentLine\": {\n      \"pattern\": \"^\\\\s*//\",\n      \"note\": \"Valid inside every fence. Ignored by validation; shown in the preview unless comments are turned off. Config comments always stay hidden.\"\n    },\n    \"required\": [\"Config\"],\n    \"duplicates\": \"Each part name may be declared once per document.\"\n  },\n  \"fences\": [\n    { \"header\": \"Config\", \"className\": \"OLConfig\", \"kind\": \"config\", \"allowsNumbering\": false, \"required\": true, \"structureCode\": null, \"bodyRule\": \"config\" },\n    { \"header\": \"Intro\", \"className\": \"OLIntro\", \"kind\": \"intro\", \"allowsNumbering\": false, \"required\": false, \"structureCode\": \"I\", \"bodyRule\": \"mixed\" },\n    { \"header\": \"Final-Chorus\", \"className\": \"OLFinalChorus\", \"kind\": \"lyric\", \"allowsNumbering\": false, \"required\": false, \"structureCode\": \"F\", \"bodyRule\": \"lyric\" },\n    { \"header\": \"Pre-Chorus\", \"className\": \"OLPreChorus\", \"kind\": \"lyric\", \"allowsNumbering\": true, \"required\": false, \"structureCode\": \"P\", \"bodyRule\": \"lyric\" },\n    { \"header\": \"Post-Chorus\", \"className\": \"OLPostChorus\", \"kind\": \"lyric\", \"allowsNumbering\": true, \"required\": false, \"structureCode\": \"X\", \"bodyRule\": \"lyric\" },\n    { \"header\": \"Refrain\", \"className\": \"OLRefrain\", \"kind\": \"lyric\", \"allowsNumbering\": true, \"required\": false, \"structureCode\": \"R\", \"bodyRule\": \"lyric\" },\n    { \"header\": \"Bridge\", \"className\": \"OLBridge\", \"kind\": \"lyric\", \"allowsNumbering\": true, \"required\": false, \"structureCode\": \"B\", \"bodyRule\": \"lyric\" },\n    { \"header\": \"Chorus\", \"className\": \"OLChorus\", \"kind\": \"lyric\", \"allowsNumbering\": true, \"required\": false, \"structureCode\": \"C\", \"bodyRule\": \"lyric\" },\n    { \"header\": \"Verse\", \"className\": \"OLVerse\", \"kind\": \"lyric\", \"allowsNumbering\": true, \"required\": false, \"structureCode\": \"V\", \"bodyRule\": \"lyric\" },\n    { \"header\": \"Note\", \"className\": \"OLNote\", \"kind\": \"lyric\", \"allowsNumbering\": true, \"required\": false, \"structureCode\": \"N\", \"bodyRule\": \"lyric\" },\n    { \"header\": \"Tag\", \"className\": \"OLTag\", \"kind\": \"lyric\", \"allowsNumbering\": true, \"required\": false, \"structureCode\": \"T\", \"bodyRule\": \"lyric\" },\n    { \"header\": \"Turnaround\", \"className\": \"OLTurnaround\", \"kind\": \"turnaround\", \"allowsNumbering\": true, \"required\": false, \"structureCode\": \"TU\", \"bodyRule\": \"mixed\" },\n    { \"header\": \"Outro\", \"className\": \"OLOutro\", \"kind\": \"outro\", \"allowsNumbering\": false, \"required\": false, \"structureCode\": \"O\", \"bodyRule\": \"mixed\" },\n    { \"header\": \"Instrumental\", \"className\": \"OLInstrumental\", \"kind\": \"instrumental\", \"allowsNumbering\": true, \"required\": false, \"structureCode\": \"IS\", \"bodyRule\": \"progression\" },\n    { \"header\": \"Interlude\", \"className\": \"OLInterlude\", \"kind\": \"instrumental\", \"allowsNumbering\": true, \"required\": false, \"structureCode\": \"L\", \"bodyRule\": \"progression\" },\n    { \"header\": \"Breakdown\", \"className\": \"OLBreakdown\", \"kind\": \"freeText\", \"allowsNumbering\": true, \"required\": false, \"structureCode\": \"D\", \"bodyRule\": \"freeText\" },\n    { \"header\": \"Vamp\", \"className\": \"OLVamp\", \"kind\": \"freeText\", \"allowsNumbering\": false, \"required\": false, \"structureCode\": \"A\", \"bodyRule\": \"freeText\" },\n    { \"header\": \"Solo\", \"className\": \"OLSolo\", \"kind\": \"freeText\", \"allowsNumbering\": true, \"required\": false, \"structureCode\": \"S\", \"bodyRule\": \"freeText\" }\n  ],\n  \"bodyRules\": {\n    \"config\": {\n      \"appliesTo\": [\"Config\"],\n      \"description\": \"Field lines of the form '- Field: value'. Indented continuation lines are allowed only under Description, Attachments and Strumming Patterns.\",\n      \"entryPattern\": \"^\\\\s*-\\\\s*(<known field>)\\\\s*:(.*)$\"\n    },\n    \"lyric\": {\n      \"appliesTo\": [\"Verse\", \"Chorus\", \"Pre-Chorus\", \"Post-Chorus\", \"Bridge\", \"Refrain\", \"Tag\", \"Note\", \"Final-Chorus\"],\n      \"description\": \"Free lyric text. Only two checks: every '[' must open a valid chord annotation and close on the same line, and a bare ']' is an error. Leading and interior '|' bar markers are allowed. An indented line under a lyric line reads as its translation line.\"\n    },\n    \"progression\": {\n      \"appliesTo\": [\"Instrumental\", \"Interlude\"],\n      \"description\": \"The whole body is joined into one chord progression. It may open with a single {c: ...} cue; everything after that must be bar tokens, chord symbols and (Nx) repeat suffixes. No lyric text.\"\n    },\n    \"mixed\": {\n      \"appliesTo\": [\"Intro\", \"Outro\", \"Turnaround\"],\n      \"description\": \"Each line is classified on its own. A line reads as a progression when it contains a '|' AND at least one whole-token chord symbol, or when it starts with '{p:' or '{c:'; every other line reads as a lyric line.\",\n      \"caution\": \"A lyric line that uses '|' separators and also contains a standalone chord-looking word (e.g. '| Hello | D |') is classified as a progression and its words are flagged as invalid tokens. Attach chords as [D] annotations instead.\"\n    },\n    \"freeText\": {\n      \"appliesTo\": [\"Breakdown\", \"Vamp\", \"Solo\"],\n      \"description\": \"Not validated. Spoken cues, ad-lib directions, arrangement notes.\"\n    }\n  },\n  \"inline\": {\n    \"chordSymbol\": {\n      \"source\": \"[A-G](?:#|b)?(?:(?:maj|min|m|dim|aug)(?:2|4|5|6|7|9|11|13)?|sus(?:2|4)?|(?:add|no|omit)(?:2|4|5|6|7|9|11|13)|(?:2|4|5|6|7|9|11|13))?(?:\\\\/[A-G](?:#|b)?)?\",\n      \"parts\": {\n        \"root\": \"[A-G] with an optional # or b.\",\n        \"decoration\": \"At most ONE of: a quality (maj, min, m, dim, aug) with an optional extension; sus / sus2 / sus4; add|no|omit + extension; or a bare extension.\",\n        \"extensions\": [\"2\", \"4\", \"5\", \"6\", \"7\", \"9\", \"11\", \"13\"],\n        \"slashBass\": \"Optional /<root>, e.g. D/F#.\"\n      },\n      \"valid\": [\"C\", \"Am\", \"Bm7\", \"Em7\", \"Cadd9\", \"Gsus4\", \"Cmaj7\", \"D/F#\", \"F#m\", \"Bb\", \"Ebm\", \"A/C#\"],\n      \"invalid\": [\n        \"C7sus4 - only one decoration group is allowed\",\n        \"Cm7b5 - no altered-fifth suffix\",\n        \"H - the root must be A-G\",\n        \"Gadd - add/no/omit require an extension\"\n      ]\n    },\n    \"chordAnnotation\": {\n      \"pattern\": \"^\\\\[<chordSymbol>\\\\]$\",\n      \"usage\": \"Inline in a lyric line, immediately before the syllable the chord lands on.\"\n    },\n    \"barTokens\": [\"||:\", \"|:\", \":||\", \":|\", \"|\"],\n    \"repeatSuffix\": {\n      \"pattern\": \"^\\\\([1-9]\\\\d*x\\\\)\",\n      \"examples\": [\"(2x)\", \"(4x)\", \"(12x)\"],\n      \"rejected\": [\"(02x)\", \"( 2x)\", \"(2x )\", \"(x2)\", \"(2X)\"],\n      \"scope\": \"Progression lines only. Inside a Structure value the compact form x2 is used instead.\"\n    },\n    \"directives\": {\n      \"strummingPattern\": {\n        \"pattern\": \"^\\\\{p:\\\\s*#[1-9]\\\\d*\\\\s*\\\\}\",\n        \"example\": \"{p: #2}\",\n        \"meaning\": \"Play this section with the Nth pattern from the Config Strumming Patterns list (1-based, in listed order).\",\n        \"allowedIn\": [\"Intro\", \"Outro\", \"Turnaround\"]\n      },\n      \"cue\": {\n        \"pattern\": \"^\\\\{c:\\\\s*[A-Za-z0-9 +\\\\-\\\\/#]+\\\\s*\\\\}\",\n        \"example\": \"{c: Piano + Pads }\",\n        \"meaning\": \"An arrangement cue for the section.\",\n        \"allowedIn\": [\"Intro\", \"Outro\", \"Turnaround\", \"Instrumental\", \"Interlude\"],\n        \"characterSet\": \"Letters, digits, space, +, -, / and # only.\"\n      },\n      \"position\": \"A directive must be the first token of its line (mixed sections) or of the body (Instrumental / Interlude).\"\n    },\n    \"markdown\": {\n      \"supported\": [\"**bold**\", \"*italic*\", \"<font color=\\\"#0f766e\\\">colored</font>\"],\n      \"note\": \"Inline Markdown renders inside fence bodies and does not interfere with chord alignment.\"\n    },\n    \"translationLine\": {\n      \"form\": \"An indented line directly under a lyric line.\",\n      \"note\": \"Renders paired with the line above it, and may omit chord annotations.\"\n    }\n  },\n  \"config\": {\n    \"fields\": [\"Title\", \"Subtitle\", \"Description\", \"Artist\", \"Copyright\", \"Locales\", \"Key\", \"Tempo\", \"Time\", \"Theme\", \"Structure\", \"Genre\", \"Style\", \"Keywords\", \"Year\", \"Melody\", \"Attachments\", \"Strumming Patterns\"],\n    \"required\": [\"Title\", \"Structure\"],\n    \"multiline\": [\"Description\", \"Attachments\", \"Strumming Patterns\"],\n    \"aliases\": { \"Strumming Pattern\": \"Strumming Patterns\" },\n    \"enums\": {\n      \"Key\": [\"C\", \"Db\", \"D\", \"Eb\", \"E\", \"F\", \"F#\", \"Gb\", \"G\", \"Ab\", \"A\", \"Bb\", \"B\", \"Am\", \"Bbm\", \"Bm\", \"Cm\", \"C#m\", \"Dm\", \"D#m\", \"Ebm\", \"Em\", \"Fm\", \"F#m\", \"Gm\", \"G#m\"],\n      \"Time\": [\"4/4\", \"2/2\", \"2/4\", \"3/4\", \"3/8\", \"6/8\", \"9/8\", \"12/8\"]\n    },\n    \"patterns\": { \"Tempo\": \"^[1-9]\\\\d*bpm$\", \"Year\": \"^[1-9]\\\\d{3}$\" },\n    \"locales\": {\n      \"separator\": \",\",\n      \"caseInsensitiveMatch\": false,\n      \"duplicatesRejected\": true,\n      \"note\": \"A closed value set - the Windows LCID tag list, written as listed. A tag outside it is an error, and so is a listed tag in another case (en-us for en-US): its message names the listed form.\",\n      \"values\": [\n        \"arc\", \"af-ZA\", \"am-ET\", \"ar-AE\", \"ar-BH\", \"ar-DZ\", \"ar-EG\", \"ar-IQ\",\n        \"ar-JO\", \"ar-KW\", \"ar-LB\", \"ar-LY\", \"ar-MA\", \"arn-CL\", \"ar-OM\", \"ar-QA\",\n        \"ar-SA\", \"ar-SD\", \"ar-SY\", \"ar-TN\", \"ar-YE\", \"as-IN\", \"az-az\", \"az-Cyrl-AZ\",\n        \"az-Latn-AZ\", \"ba-RU\", \"be-BY\", \"bg-BG\", \"bn-BD\", \"bn-IN\", \"bo-CN\", \"br-FR\",\n        \"bs-Cyrl-BA\", \"bs-Latn-BA\", \"ca-ES\", \"co-FR\", \"cs-CZ\", \"cy-GB\", \"da-DK\", \"de-AT\",\n        \"de-CH\", \"de-DE\", \"de-LI\", \"de-LU\", \"dsb-DE\", \"dv-MV\", \"el-CY\", \"el-GR\",\n        \"en-029\", \"en-AU\", \"en-BZ\", \"en-CA\", \"en-cb\", \"en-GB\", \"en-IE\", \"en-IN\",\n        \"en-JM\", \"en-MT\", \"en-MY\", \"en-NZ\", \"en-PH\", \"en-SG\", \"en-TT\", \"en-US\",\n        \"en-ZA\", \"en-ZW\", \"es-AR\", \"es-BO\", \"es-CL\", \"es-CO\", \"es-CR\", \"es-DO\",\n        \"es-EC\", \"es-ES\", \"es-GT\", \"es-HN\", \"es-MX\", \"es-NI\", \"es-PA\", \"es-PE\",\n        \"es-PR\", \"es-PY\", \"es-SV\", \"es-US\", \"es-UY\", \"es-VE\", \"et-EE\", \"eu-ES\",\n        \"fa-IR\", \"fi-FI\", \"fil-PH\", \"fo-FO\", \"fr-BE\", \"fr-CA\", \"fr-CH\", \"fr-FR\",\n        \"fr-LU\", \"fr-MC\", \"fy-NL\", \"ga-IE\", \"gd-GB\", \"gd-ie\", \"gl-ES\", \"gsw-FR\",\n        \"gu-IN\", \"ha-Latn-NG\", \"he-IL\", \"hi-IN\", \"hr-BA\", \"hr-HR\", \"hsb-DE\", \"hu-HU\",\n        \"hy-AM\", \"id-ID\", \"ig-NG\", \"ii-CN\", \"in-ID\", \"is-IS\", \"it-CH\", \"it-IT\",\n        \"iu-Cans-CA\", \"iu-Latn-CA\", \"iw-IL\", \"ja-JP\", \"ka-GE\", \"kk-KZ\", \"kl-GL\", \"km-KH\",\n        \"kn-IN\", \"kok-IN\", \"ko-KR\", \"ky-KG\", \"lb-LU\", \"lo-LA\", \"lt-LT\", \"lv-LV\",\n        \"mi-NZ\", \"mk-MK\", \"ml-IN\", \"mn-MN\", \"mn-Mong-CN\", \"moh-CA\", \"mr-IN\", \"ms-BN\",\n        \"ms-MY\", \"mt-MT\", \"nb-NO\", \"ne-NP\", \"nl-BE\", \"nl-NL\", \"nn-NO\", \"no-no\",\n        \"nso-ZA\", \"oc-FR\", \"or-IN\", \"pa-IN\", \"pl-PL\", \"prs-AF\", \"ps-AF\", \"pt-BR\",\n        \"pt-PT\", \"qut-GT\", \"quz-BO\", \"quz-EC\", \"quz-PE\", \"rm-CH\", \"ro-mo\", \"ro-RO\",\n        \"ru-mo\", \"ru-RU\", \"rw-RW\", \"sah-RU\", \"sa-IN\", \"se-FI\", \"se-NO\", \"se-SE\",\n        \"si-LK\", \"sk-SK\", \"sl-SI\", \"sma-NO\", \"sma-SE\", \"smj-NO\", \"smj-SE\", \"smn-FI\",\n        \"sms-FI\", \"sq-AL\", \"sr-BA\", \"sr-CS\", \"sr-Cyrl-BA\", \"sr-Cyrl-CS\", \"sr-Cyrl-ME\", \"sr-Cyrl-RS\",\n        \"sr-Latn-BA\", \"sr-Latn-CS\", \"sr-Latn-ME\", \"sr-Latn-RS\", \"sr-ME\", \"sr-RS\", \"sr-sp\", \"sv-FI\",\n        \"sv-SE\", \"sw-KE\", \"syr-SY\", \"ta-IN\", \"te-IN\", \"tg-Cyrl-TJ\", \"th-TH\", \"tk-TM\",\n        \"tlh-QS\", \"tn-ZA\", \"tr-TR\", \"tt-RU\", \"tzm-Latn-DZ\", \"ug-CN\", \"uk-UA\", \"ur-PK\",\n        \"uz-Cyrl-UZ\", \"uz-Latn-UZ\", \"uz-uz\", \"vi-VN\", \"wo-SN\", \"xh-ZA\", \"yo-NG\", \"zh-CN\",\n        \"zh-HK\", \"zh-MO\", \"zh-SG\", \"zh-TW\", \"zu-ZA\"\n      ]\n    },\n    \"attachments\": {\n      \"valueForms\": [\"<scheme>://<url>\", \"[label](<scheme>://<url>)\"],\n      \"pattern\": \"^(?:(?:[A-Za-z][A-Za-z0-9+.-]*:\\\\/\\\\/\\\\S[^\\\\r\\\\n]*)|\\\\[[^\\\\]\\\\r\\\\n]+\\\\]\\\\((?:[A-Za-z][A-Za-z0-9+.-]*:\\\\/\\\\/\\\\S[^\\\\r\\\\n)]*)\\\\))$\",\n      \"detectedTypes\": [\"youtube\", \"audio\", \"video\", \"pdf\", \"image\", \"other\"],\n      \"note\": \"One attachment per line; further attachments go on indented continuation lines.\"\n    },\n    \"strummingPatterns\": {\n      \"stepCharacters\": [\"d\", \"D\", \"v\", \"V\", \"u\", \"U\", \"^\", \"x\", \"X\", \"1\", \"*\", \"+\", \"-\", \"_\", \".\", \"0\"],\n      \"separators\": [\"|\", \" \", \"\\t\"],\n      \"example\": \"d--u-- | d-u---\",\n      \"note\": \"One pattern per indented line under the field. A // comment line above a pattern becomes its label in the preview. Patterns are numbered from 1 in listed order and referenced by {p: #N}.\"\n    }\n  },\n  \"structure\": {\n    \"purpose\": \"The Config Structure field is the performance order of the song, written as one compact token string.\",\n    \"syntaxExample\": \"IV1x2CV1V2CO\",\n    \"codes\": [\n      { \"code\": \"I\", \"header\": \"Intro\", \"allowsNumbering\": false },\n      { \"code\": \"V\", \"header\": \"Verse\", \"allowsNumbering\": true },\n      { \"code\": \"N\", \"header\": \"Note\", \"allowsNumbering\": true },\n      { \"code\": \"P\", \"header\": \"Pre-Chorus\", \"allowsNumbering\": true },\n      { \"code\": \"C\", \"header\": \"Chorus\", \"allowsNumbering\": true },\n      { \"code\": \"X\", \"header\": \"Post-Chorus\", \"allowsNumbering\": true },\n      { \"code\": \"F\", \"header\": \"Final-Chorus\", \"allowsNumbering\": false },\n      { \"code\": \"B\", \"header\": \"Bridge\", \"allowsNumbering\": true },\n      { \"code\": \"IS\", \"header\": \"Instrumental\", \"allowsNumbering\": true },\n      { \"code\": \"L\", \"header\": \"Interlude\", \"allowsNumbering\": true },\n      { \"code\": \"D\", \"header\": \"Breakdown\", \"allowsNumbering\": true },\n      { \"code\": \"R\", \"header\": \"Refrain\", \"allowsNumbering\": true },\n      { \"code\": \"T\", \"header\": \"Tag\", \"allowsNumbering\": true },\n      { \"code\": \"TU\", \"header\": \"Turnaround\", \"allowsNumbering\": true },\n      { \"code\": \"A\", \"header\": \"Vamp\", \"allowsNumbering\": false },\n      { \"code\": \"S\", \"header\": \"Solo\", \"allowsNumbering\": true },\n      { \"code\": \"O\", \"header\": \"Outro\", \"allowsNumbering\": false }\n    ],\n    \"matching\": \"Codes are matched longest-first, so IS reads as Instrumental, never Intro + Solo.\",\n    \"index\": { \"pattern\": \"[1-9]\\\\d*\", \"note\": \"Written immediately after the code (V1), and only for a section that allows numbering.\" },\n    \"repeat\": { \"pattern\": \"x[1-9]\\\\d*\", \"note\": \"Written after the code and index (V1x2 = play Verse 1 twice). The order is the reverse of the (2x) used in a progression body.\" },\n    \"rules\": [\n      \"No whitespace or separators anywhere in the value.\",\n      \"Every token must name a part the document actually declares as a fence.\",\n      \"The same part may not appear twice in a row; raise the previous token's repeat count instead.\"\n    ]\n  },\n  \"diagnostics\": [\n    { \"message\": \"Use ol:Config. Lowercase ol:config is not supported.\", \"cause\": \"The header spelled in lowercase.\", \"fix\": \"Config\" },\n    { \"message\": \"Config fences cannot be numbered or suffixed.\", \"cause\": \"ol:Config 1 or similar.\" },\n    { \"message\": \"<Header> fences cannot be numbered.\", \"cause\": \"An index on Intro, Outro, Vamp, Final-Chorus or Config.\" },\n    { \"message\": \"Section indexes must start at 1.\", \"cause\": \"A zero or zero-padded index, e.g. ol:Verse 01.\" },\n    { \"message\": \"Unsupported ol part. Use Config, Intro, Instrumental, Interlude, Turnaround, lyric sections, Breakdown, Vamp, or Solo.\", \"cause\": \"An unknown fence header.\" },\n    { \"message\": \"Unsupported ol part. Did you mean ol:<Header>?\", \"cause\": \"An unknown header close to a known one (a letter or two off, or only case, spaces or hyphens apart).\", \"fix\": \"<Header>\" },\n    { \"message\": \"Duplicate ol part. <partName> is already declared on line N.\", \"cause\": \"The same part name declared twice.\" },\n    { \"message\": \"Unclosed ol fence.\", \"cause\": \"A missing closing fence line.\" },\n    { \"message\": \"Missing required ol part. Add ol:Config.\", \"cause\": \"No Config fence in the document.\" },\n    { \"message\": \"Invalid config entry. Use - Field: value.\", \"cause\": \"A '-' line with no 'Field:', such as '- Genre'.\" },\n    { \"message\": \"Unsupported config field. Use ...\", \"cause\": \"A '- Field: value' entry whose field is not a Config field nor close to one, such as '- Colour: red'. The message lists them all.\" },\n    { \"message\": \"Unsupported config field. Did you mean <Field>?\", \"cause\": \"An unknown field close to a known one (a letter or two off, or only case, spaces or hyphens apart), such as '- title:' or '- Strucure:'. Never a field the Config already declares, nor one an earlier misspelt name was pointed at.\", \"fix\": \"<Field>\" },\n    { \"message\": \"Config continuation lines must follow a Description, Attachments, or Strumming Patterns entry.\", \"cause\": \"A line that is not a '- Field:' entry, indented or not, after a single-line field.\" },\n    { \"message\": \"Duplicate config field. <Field> is already declared on line N.\", \"cause\": \"A Config field written twice.\" },\n    { \"message\": \"<Field> must provide a value on the same line.\", \"cause\": \"A single-line field left empty with its value on the next line.\" },\n    { \"message\": \"<Field> must be one of: ...\", \"cause\": \"A Key or Time value outside its enum.\", \"fix\": \": <value>, when only case, spaces or a sharp/flat sign set it apart from one (not a Key ending in a capital M)\" },\n    { \"message\": \"Tempo must be a whole number of beats per minute then bpm, such as 76bpm.\", \"cause\": \"Tempo written as '70 bpm', '70', or '0bpm'.\", \"fix\": \": <n>bpm, unless the count is 0 or has a fraction\" },\n    { \"message\": \"Year must be a four-digit year, such as 2024.\", \"cause\": \"Year written as '24', '2023-2024', or with other-script digits.\" },\n    { \"message\": \"Missing required config fields: ...\", \"cause\": \"Title or Structure is absent from Config.\" },\n    { \"message\": \"Locales must be a comma-separated list of locales with no empty entry.\", \"cause\": \"A trailing comma or an empty slot.\" },\n    { \"message\": \"Duplicate locale. <tag> is already listed.\", \"cause\": \"The same locale tag listed twice.\" },\n    { \"message\": \"Unsupported locale. Use <tag> instead of <typed>.\", \"cause\": \"A listed tag in another case, such as en-us.\", \"fix\": \"<tag>\" },\n    { \"message\": \"Unsupported locale. <typed> is not a supported locale such as en-US or km-KH.\", \"cause\": \"A tag outside the closed set.\" },\n    { \"message\": \"Attachments must use a protocol-based URL such as http://, https://, file:///, ftp://, ftps://, or a Markdown link whose target is such a URL. Spaces inside the URL are allowed.\", \"cause\": \"An Attachments value that is neither a scheme:// URL nor a Markdown link to one, such as demo.mp3.\" },\n    { \"message\": \"Attachments continuation lines must start with spaces or tabs and contain a protocol-based URL such as http://, https://, file:///, ftp://, ftps://, or a Markdown link that points to one. Spaces inside the URL are allowed.\", \"cause\": \"A line under Attachments that is not indented, or holds no such URL.\" },\n    { \"message\": \"Strumming Patterns must use only d, D, v, V, u, U, ^, x, X, 1, *, +, -, _, ., 0, bar separators (|), and spaces or tabs.\", \"cause\": \"Any other character inside a pattern.\" },\n    { \"message\": \"Strumming Patterns continuation lines must start with spaces or tabs and use only d, D, v, V, u, U, ^, x, X, 1, *, +, -, _, ., 0, bar separators (|), and spaces or tabs.\", \"cause\": \"A line under Strumming Patterns that is not indented, or holds any other character.\" },\n    { \"message\": \"Structure must use compact codes like IV1x2CV1V2CO.\", \"cause\": \"Whitespace inside the Structure value.\" },\n    { \"message\": \"Unknown structure code. Use ...\", \"cause\": \"A letter that is not a structure code.\" },\n    { \"message\": \"<Header> cannot be numbered in Structure.\", \"cause\": \"An index on a code whose section is unnumbered.\" },\n    { \"message\": \"Repeat suffix must use compact format x2.\", \"cause\": \"'x' written without a count in Structure.\" },\n    { \"message\": \"Repeat counts must start at 1.\", \"cause\": \"x0 or x02 in Structure.\" },\n    { \"message\": \"Structure cannot place <part> twice in a row. Increase the previous token's repeat count instead.\", \"cause\": \"CC instead of Cx2.\" },\n    { \"message\": \"Structure references undeclared ol part. <part> is not declared.\", \"cause\": \"A Structure token with no matching fence; every such token is marked.\" },\n    { \"message\": \"Unclosed chord annotation.\", \"cause\": \"A '[' with no ']' on the same line.\" },\n    { \"message\": \"Invalid chord annotation.\", \"cause\": \"A bracketed token that is not a chord symbol and is not close to one, such as [Hmm].\" },\n    { \"message\": \"Invalid chord annotation. Try [<chord>].\", \"cause\": \"A bracketed token close to a chord symbol; the suggestion is that chord.\", \"fix\": \"[<chord>]\" },\n    { \"message\": \"Unexpected closing bracket in lyric line.\", \"cause\": \"A ']' with no opening '['.\" },\n    { \"message\": \"Invalid <section> token \\\"<token>\\\". Try <chord>.\", \"cause\": \"A progression word that is nearly a chord: bracketed ([G]), lowercase (em) or German B (Hm).\", \"fix\": \"<chord>\" },\n    { \"message\": \"Invalid <section> token \\\"<token>\\\". Use chords, | bars and (2x) repeats.\", \"cause\": \"Any other word in a progression that is neither a chord, a bar token, nor a repeat suffix.\" },\n    { \"message\": \"Invalid <section> directive. Expected {c: Piano + Pads }.\", \"cause\": \"A malformed directive opening an Instrumental / Interlude body.\" },\n    { \"message\": \"Invalid <section> directive. Expected {p: #3} or {c: Piano + Pads }.\", \"cause\": \"A malformed directive on a mixed-section progression line.\" },\n    { \"message\": \"Repeat suffix must use exact format (2x).\", \"cause\": \"A repeat-looking token such as (2 x) or (2X).\", \"fix\": \"(<n>x), unless the count is wrong\" },\n    { \"message\": \"Unclosed repeat suffix.\", \"cause\": \"A '(' with no ')' in a progression.\" }\n  ]\n}\n````\n\n### 8.2 Song schema (JSON Schema draft 2020-12)\n\nA song as a structured object — `config` plus ordered `sections`. Validate\nagainst this before serializing to notation, and every rule of §1–§5 that a\nschema can carry is enforced for you.\n\n```json\n{\n  \"$schema\": \"https://json-schema.org/draft/2020-12/schema\",\n  \"$id\": \"https://open-lyric.org/schema/song.schema.json\",\n  \"title\": \"Open Lyric song\",\n  \"description\": \"A song as a structured object, serializable to Open Lyric notation.\",\n  \"type\": \"object\",\n  \"required\": [\"config\", \"sections\"],\n  \"additionalProperties\": false,\n  \"properties\": {\n    \"config\": { \"$ref\": \"#/$defs/config\" },\n    \"sections\": {\n      \"type\": \"array\",\n      \"minItems\": 1,\n      \"items\": { \"$ref\": \"#/$defs/section\" },\n      \"description\": \"The fences of the document, in written order. Part names must be unique.\"\n    }\n  },\n  \"$defs\": {\n    \"chordSymbol\": {\n      \"type\": \"string\",\n      \"pattern\": \"^[A-G](?:#|b)?(?:(?:maj|min|m|dim|aug)(?:2|4|5|6|7|9|11|13)?|sus(?:2|4)?|(?:add|no|omit)(?:2|4|5|6|7|9|11|13)|(?:2|4|5|6|7|9|11|13))?(?:\\\\/[A-G](?:#|b)?)?$\",\n      \"examples\": [\"C\", \"Am\", \"Bm7\", \"Cadd9\", \"Gsus4\", \"Cmaj7\", \"D/F#\"]\n    },\n    \"sectionHeader\": {\n      \"type\": \"string\",\n      \"enum\": [\n        \"Intro\", \"Verse\", \"Pre-Chorus\", \"Chorus\", \"Post-Chorus\", \"Final-Chorus\",\n        \"Bridge\", \"Refrain\", \"Tag\", \"Note\", \"Instrumental\", \"Interlude\",\n        \"Turnaround\", \"Outro\", \"Breakdown\", \"Vamp\", \"Solo\"\n      ]\n    },\n    \"unnumberedHeader\": {\n      \"type\": \"string\",\n      \"enum\": [\"Intro\", \"Outro\", \"Vamp\", \"Final-Chorus\"]\n    },\n    \"localeTag\": {\n      \"type\": \"string\",\n      \"description\": \"One tag of the closed locale set enumerated in the grammar of section 8.1 under config.locales.values.\",\n      \"pattern\": \"^[A-Za-z]{2,4}(?:-[A-Za-z0-9]{2,8}){0,2}$\",\n      \"examples\": [\"en-US\", \"km-KH\", \"fr-FR\", \"zh-CN\"]\n    },\n    \"config\": {\n      \"type\": \"object\",\n      \"description\": \"The ol:Config fence.\",\n      \"required\": [\"Title\", \"Structure\"],\n      \"additionalProperties\": false,\n      \"properties\": {\n        \"Title\": { \"type\": \"string\", \"minLength\": 1 },\n        \"Subtitle\": { \"type\": \"string\" },\n        \"Description\": {\n          \"type\": \"array\",\n          \"items\": { \"type\": \"string\" },\n          \"description\": \"One entry per line; lines after the first are written indented.\"\n        },\n        \"Artist\": { \"type\": \"string\", \"minLength\": 1 },\n        \"Copyright\": { \"type\": \"string\", \"minLength\": 1 },\n        \"Locales\": {\n          \"type\": \"array\",\n          \"items\": { \"$ref\": \"#/$defs/localeTag\" },\n          \"uniqueItems\": true,\n          \"description\": \"Serialized as one comma-separated line.\"\n        },\n        \"Key\": {\n          \"type\": \"string\",\n          \"enum\": [\n            \"C\", \"Db\", \"D\", \"Eb\", \"E\", \"F\", \"F#\", \"Gb\", \"G\", \"Ab\", \"A\", \"Bb\", \"B\",\n            \"Am\", \"Bbm\", \"Bm\", \"Cm\", \"C#m\", \"Dm\", \"D#m\", \"Ebm\", \"Em\", \"Fm\", \"F#m\",\n            \"Gm\", \"G#m\"\n          ]\n        },\n        \"Tempo\": { \"type\": \"string\", \"pattern\": \"^[1-9]\\\\d*bpm$\", \"examples\": [\"68bpm\", \"120bpm\"] },\n        \"Time\": { \"type\": \"string\", \"enum\": [\"4/4\", \"2/2\", \"2/4\", \"3/4\", \"3/8\", \"6/8\", \"9/8\", \"12/8\"] },\n        \"Theme\": { \"type\": \"string\" },\n        \"Structure\": {\n          \"type\": \"string\",\n          \"pattern\": \"^(?:(?:IS|TU|[IVNPCXFBLDRTASO])(?:[1-9]\\\\d*)?(?:x[1-9]\\\\d*)?)+$\",\n          \"description\": \"Compact performance order. Codes are matched longest-first. Beyond this pattern: every token must name a declared section, no token may repeat the previous one, and only a numbered section may carry an index.\",\n          \"examples\": [\"IV1x2CV1V2CO\", \"IV1PCXV2CO\"]\n        },\n        \"Genre\": { \"type\": \"string\" },\n        \"Style\": { \"type\": \"string\" },\n        \"Keywords\": {\n          \"type\": \"array\",\n          \"items\": { \"type\": \"string\", \"pattern\": \"^[^,]+$\" },\n          \"description\": \"Serialized as one comma-separated line.\"\n        },\n        \"Year\": { \"type\": \"string\", \"pattern\": \"^[1-9]\\\\d{3}$\", \"examples\": [\"2024\"] },\n        \"Melody\": { \"type\": \"string\", \"description\": \"The tune the lyrics are sung to.\" },\n        \"Attachments\": {\n          \"type\": \"array\",\n          \"items\": {\n            \"type\": \"string\",\n            \"pattern\": \"^(?:(?:[A-Za-z][A-Za-z0-9+.-]*:\\\\/\\\\/\\\\S[^\\\\r\\\\n]*)|\\\\[[^\\\\]\\\\r\\\\n]+\\\\]\\\\((?:[A-Za-z][A-Za-z0-9+.-]*:\\\\/\\\\/\\\\S[^\\\\r\\\\n)]*)\\\\))$\"\n          },\n          \"description\": \"A bare URL or a Markdown link, one per line.\"\n        },\n        \"Strumming Patterns\": {\n          \"type\": \"array\",\n          \"description\": \"One pattern per line, in reference order: {p: #1} is the first entry.\",\n          \"items\": {\n            \"type\": \"object\",\n            \"required\": [\"pattern\"],\n            \"additionalProperties\": false,\n            \"properties\": {\n              \"label\": { \"type\": \"string\", \"description\": \"Written above the pattern as a // comment line.\" },\n              \"pattern\": {\n                \"type\": \"string\",\n                \"pattern\": \"^[dDvVuU^xX1*+_.0\\\\-| \\t]+$\",\n                \"examples\": [\"d--u-- | d-u---\"]\n              }\n            }\n          }\n        }\n      }\n    },\n    \"section\": {\n      \"type\": \"object\",\n      \"required\": [\"header\", \"lines\"],\n      \"additionalProperties\": false,\n      \"properties\": {\n        \"header\": { \"$ref\": \"#/$defs/sectionHeader\" },\n        \"index\": {\n          \"type\": \"integer\",\n          \"minimum\": 1,\n          \"description\": \"Appended to the header to form the part name ('Verse 2'). Only for a section that allows numbering.\"\n        },\n        \"lines\": {\n          \"type\": \"array\",\n          \"items\": { \"type\": \"string\" },\n          \"description\": \"The fence body, one entry per line. A '//' line is a comment. An indented line under a lyric line is its translation.\"\n        }\n      },\n      \"allOf\": [\n        {\n          \"if\": { \"properties\": { \"header\": { \"$ref\": \"#/$defs/unnumberedHeader\" } }, \"required\": [\"header\"] },\n          \"then\": { \"not\": { \"required\": [\"index\"] } }\n        }\n      ]\n    }\n  }\n}\n```\n\n### 8.3 Rules a schema cannot carry\n\nValidate these yourself; they are cross-references, not shapes.\n\n1. Part names are unique across `sections`.\n2. Every `Structure` token names a section the document declares.\n3. No `Structure` token repeats the one before it — raise its repeat count.\n4. Only a numbered section may carry an index, in `Structure` as in a header.\n5. Body lines must satisfy the section's body rule (§2): lyric, progression,\n   mixed, or free text.\n6. `{p: #N}` must point at an existing `Strumming Patterns` entry.\n";
//#endregion
//#region src/plugins/OpenLyric/examples/catalog.ts
var OPEN_LYRIC_EXAMPLES = [
	{
		id: "example1",
		fileName: "example1.ol.md",
		title: "Extended Worship Build",
		description: "Extended worship flow with multiple bridges, instrumentals, repeat counts, and a final chorus.",
		content: example1_ol_default
	},
	{
		id: "example2-rich-config",
		fileName: "example2-rich-config.ol.md",
		title: "Quiet River at Dawn",
		description: "Rich config fields: subtitle, multiline description, attachments, strumming patterns, pre-chorus, and post-chorus.",
		content: "# Quiet River at Dawn\n\nUse this example to test rich config fields, including subtitle, multiline description, attachments, strumming patterns, pre-chorus, and post-chorus.\n\n```ol:Config\n- Title: Quiet River at Dawn\n- Subtitle: A Soft 6/8 Prayer\n- Description:\n	A gentle worship draft for acoustic teams.\n	It demonstrates rich config fields, multiline values,\n	attachments, and strumming patterns inside one song.\n- Artist: Open Lyric Team\n- Copyright: 2026 Open Lyric\n- Locales: en-US\n- Key: G\n- Tempo: 68bpm\n- Time: 6/8\n- Theme: Quiet trust\n- Structure: IV1PCXV2PCXCO\n- Genre: Worship\n- Style: Acoustic 6/8\n- Keywords: morning, trust, acoustic worship\n- Year: 2026\n- Melody: Original tune\n- Attachments: https://example.com/audio/quiet-river-demo.mp3\n	[Piano Chart](file:///C:/Charts/quiet-river-at-dawn.pdf)\n	vscode://file/C:/OpenLyric/quiet-river-at-dawn.md\n- Strumming Patterns:\n	// Slow rolling pulse\n	d--u-- | d-u---\n	// Lift on the chorus\n	ddu--- | d-u-u-\n```\n\n```ol:Intro\n// Count in the band on bar 2\n{p: #2 } | G | D/F# | Em7 | Cadd9 | (2x)\n```\n\n```ol:Verse 1\n// Fingerpicked guitar only\nMorning breaks with mercy on the water\nEvery breath reminds me You are near\n```\n\n```ol:Pre-Chorus\n[Em7]When the waters rise, [D]You remain\n[Cadd9]Steady as the promise [D]of Your name\n```\n\n```ol:Chorus\n|[G]Carry me gently, carry me kindly\n|[D/F#]Hold me in peace when the night feels long\n// Full band lifts here\n|[Em7]Carry me gently, carry me kindly\n|[Cadd9]Teach my weak heart to become a song\n```\n\n```ol:Post-Chorus\n// Sing twice, softer the second time\n|[Em7]River of peace, keep carrying me\n|[Cadd9]River of peace, keep carrying me\n```\n\n```ol:Verse 2\nEvery hidden worry meets Your silence\nEvery scattered thought returns to rest\n```\n\n```ol:Outro\nStill You are near, still You are near\nStill You are near when the daylight fades\n// Ritard on the last line\n```\n"
	},
	{
		id: "example3-bilingual-bars",
		fileName: "example3-bilingual-bars.ol.md",
		title: "Bilingual Mercy Response",
		description: "Unicode and bilingual bar-aligned lyrics with translation pairs and chord annotations.",
		content: "# Bilingual Mercy Response\n\nUse this example to test Unicode lyrics, bilingual translation pairs, bar-aligned lyric lines, and chord annotations in the same file.\n\n```ol:Config\n- Title: Bilingual Mercy Response\n- Artist: Open Lyric Team\n- Copyright: 2026 Open Lyric\n- Key: D\n- Tempo: 72bpm\n- Time: 4/4\n- Structure: IV1CV2B1CO\n- Strumming Patterns:\n	// Slow rolling pulse\n	d--u-- | d-u---\n	// Lift on the chorus\n	ddu--- | d-u-u-\n```\n\n```ol:Intro\n| D | A/C# | Bm7 | G |\n```\n\n```ol:Verse 1\nYour mercy meets us in the morning light\nYour kindness stays with us through every night\n```\n\n```ol:Chorus\n|[D]ព្រះអង្គស្រឡាញ់ខ្ញុំ |[A/C#]ទ្រង់មិនចាកចេញ\n	You have held me close  You never walk away\n|[Bm7]ពេលយប់ងងឹតមក |[G]ពន្លឺទ្រង់នៅតែភ្លឺ\n	When the night is deep  Your light is still with me\n```\n\n```ol:Verse 2\n[D]When my strength is small, [A/C#]Your grace is strong\n[Bm7]When my song is lost, [G]You sing me home\n```\n\n```ol:Bridge 1\n// The translation line can omit chord annotations.\n|[Bm7]Holy are You Lord |[G]Faithful are You Lord\n	Holy are You Lord  Faithful are You Lord\n|[D]Mercy without end |[A/C#]Peace that makes us whole\n	Mercy without end  Peace that makes us whole\n```\n\n```ol:Outro\n|[D]Jesus, keep us near |[A/C#]Jesus, keep us near\n```\n"
	},
	{
		id: "example4-refrain-and-tags",
		fileName: "example4-refrain-and-tags.ol.md",
		title: "Refrain and Tag Lift",
		description: "Refrain plus numbered Tag sections reused from the compact structure.",
		content: "# Refrain and Tag Lift\n\nUse this example to test a Refrain section together with multiple numbered Tag sections referenced from the compact structure.\n\n```ol:Config\n- Title: Refrain and Tag Lift\n- Artist: Open Lyric Team\n- Copyright: 2026 Open Lyric\n- Key: G\n- Tempo: 78bpm\n- Time: 4/4\n- Structure: V1CRT1T2T1O\n- Strumming Patterns:\n	// Slow rolling pulse\n	d--u-- | d-u---\n	// Lift on the chorus\n	ddu--- | d-u-u-\n```\n\n```ol:Verse 1\nYou found me in the dust and called me by my name\nYou lifted all my fear and taught my heart to praise\n```\n\n```ol:Chorus\n|[G]You are worthy, forever worthy\n|[D]You are worthy, Jesus our King\n|[Em]You are worthy, forever worthy\n|[C]Let every heart rise up and sing\n```\n\n```ol:Refrain\n// Three times, quieter each pass\n|[G]Holy forever, holy forever\n```\n\n```ol:Tag 1\n|[G]You are enough, You are enough\n```\n\n```ol:Tag 2\n// Leader alone, band stops\n|[Em]More than enough for me\n```\n\n```ol:Outro\n// A cappella\nHoly forever, holy forever\n```\n"
	},
	{
		id: "example5-interlude-and-comments",
		fileName: "example5-interlude-and-comments.ol.md",
		title: "Between the Verses",
		description: "Numbered Interlude sections with drafting comments inside intro, interlude, and lyric blocks.",
		content: "# Between the Verses\n\nUse this example to test numbered Interlude sections and comment lines inside intro, interlude, and lyric fences.\n\n```ol:Config\n- Title: Between the Verses\n- Artist: Open Lyric Team\n- Copyright: 2026 Open Lyric\n- Key: D\n- Tempo: 84bpm\n- Time: 4/4\n- Structure: IV1CL1V2CL2CO\n- Strumming Patterns:\n	// Slow rolling pulse\n	d--u-- | d-u---\n	// Lift on the chorus\n	ddu--- | d-u-u-\n```\n\n```ol:Intro\n// Start with picked guitar only.\n| D | A/C# | Bm7 | G |\n```\n\n```ol:Verse 1\nWhen the room is quiet, You are still the song\nWhen my words are failing, You keep carrying on\n```\n\n```ol:Chorus\n// The chorus returns after each interlude.\n|[D]You are steady |[A/C#]You are faithful\n|[Bm7]You are stronger |[G]than the storm\n```\n\n```ol:Interlude 1\n// Guitar answers the chorus melody.\n| D | A/C# | Bm7 | G | (2x)\n```\n\n```ol:Verse 2\nEvery waiting moment leans into Your grace\nEvery hidden answer shines upon Your face\n```\n\n```ol:Interlude 2\n// Full band lift before the final chorus.\n{c: Keys + Gtr Solo } | D | A/C# | Bm7 | G | (4x)\n```\n\n```ol:Outro\nYou are steady, You are faithful\n```\n"
	},
	{
		id: "example6-breakdown-and-vamp",
		fileName: "example6-breakdown-and-vamp.ol.md",
		title: "Fire on the Altar",
		description: "Free-text Breakdown and Vamp sections for spoken cues and ad-lib directions.",
		content: "# Fire on the Altar\n\nUse this example to test free-text Breakdown and Vamp sections for spoken cues, arrangement notes, and ad-lib directions.\n\n```ol:Config\n- Title: Fire on the Altar\n- Artist: Open Lyric Team\n- Copyright: 2026 Open Lyric\n- Key: E\n- Tempo: 76bpm\n- Time: 4/4\n- Structure: IV1CB1D1ACO\n- Strumming Patterns:\n	// Slow rolling pulse\n	d--u-- | d-u---\n	// Lift on the chorus\n	ddu--- | d-u-u-\n```\n\n```ol:Intro\n| E | B | C#m | A |\n```\n\n```ol:Verse 1\nSet Your fire upon the altar of my heart\nTeach me how to live surrendered from the start\n```\n\n```ol:Chorus\n|[E]Holy flame, come [B]burn in me\n|[C#m]Light the dark and [A]set me free\n```\n\n```ol:Bridge 1\n|[A]Not by power |[B]Not by might\n// Build the toms under the second line\n|[C#m]By Your Spirit |[B]comes new life\n```\n\n```ol:Breakdown 1\n// Half-time feel\nOnly kick, piano, and one vocal line.\nLeader speaks over the final bar: \"You are holy.\"\n```\n\n```ol:Vamp\n// Hold here as long as the room needs\nRepeat | E | B | C#m | A | until the room settles.\nBand watches the leader for the next chorus entrance.\n```\n\n```ol:Outro\n{c: Piano + pads } | E | B | C#m | A |\n```\n"
	},
	{
		id: "example7-solo-variations",
		fileName: "example7-solo-variations.ol.md",
		title: "Lead Line Offering",
		description: "Numbered Solo sections paired with separate Instrumental sections and cue directives.",
		content: "# Lead Line Offering\n\nUse this example to test numbered Solo sections paired with separate Instrumental sections and cue directives.\n\n```ol:Config\n- Title: Lead Line Offering\n- Artist: Open Lyric Team\n- Copyright: 2026 Open Lyric\n- Key: A\n- Tempo: 88bpm\n- Time: 4/4\n- Structure: IV1CIS1S1B1IS2S2CO\n- Strumming Patterns:\n	// Slow rolling pulse\n	d--u-- | d-u---\n	// Lift on the chorus\n	ddu--- | d-u-u-\n```\n\n```ol:Intro\n| A | E/G# | F#m | D |\n```\n\n```ol:Verse 1\nBring the melody that only grace can write\nShape the room with wonder, set our eyes alight\n```\n\n```ol:Chorus\n|[A]Let the song rise up |[E/G#]through every open heart\n|[F#m]Let the song rise up |[D]and never fall apart\n```\n\n```ol:Instrumental 1\n{c: Gtr Solo } | A | E/G# | F#m | D | (2x)\n```\n\n```ol:Solo 1\n// Eight bars, then hand back to the vocal\nGuitar takes the chorus melody with light delay.\nKeep the drums restrained until the final bar.\n```\n\n```ol:Bridge 1\n|[D]Everything we offer |[E]You make beautiful\n|[F#m]Everything we carry |[E]You make new\n```\n\n```ol:Instrumental 2\n{c: Keys + Gtr Solo } | A | E/G# | F#m | D | (4x)\n```\n\n```ol:Solo 2\nKeys answer in octaves.\nDrums open on bar three and push into the chorus.\n// Cue the band with a nod on the last bar\n```\n\n```ol:Outro\n// Stop together on the downbeat\n{c: Full band hit } | A | E/G# | F#m | D |\n```\n"
	},
	{
		id: "example8-lyric-outro-and-final-chorus",
		fileName: "example8-lyric-outro-and-final-chorus.ol.md",
		title: "Higher Than the Morning",
		description: "Lyric outro alongside a modulated final chorus.",
		content: "# Higher Than the Morning\n\nUse this example to test a lyric outro together with a modulated Final-Chorus section.\n\n```ol:Config\n- Title: Higher Than the Morning\n- Artist: Open Lyric Team\n- Copyright: 2026 Open Lyric\n- Key: C\n- Tempo: 74bpm\n- Time: 3/4\n- Structure: IV1CV2B1FO\n- Strumming Patterns:\n	// Slow rolling pulse\n	d--u-- | d-u---\n	// Lift on the chorus\n	ddu--- | d-u-u-\n```\n\n```ol:Intro\n| C | G/B | Am | F |\n```\n\n```ol:Verse 1\nYou meet the sunrise with compassion in Your hands\nYou hold tomorrow with a wisdom that still stands\n```\n\n```ol:Chorus\n|[C]Higher than the morning |[G/B]brighter than the day\n|[Am]You are always with me |[F]showing me the way\n```\n\n```ol:Verse 2\nEvery anxious moment bows before Your peace\nEvery restless question finds its fear released\n```\n\n```ol:Bridge 1\n// Build each repeat\n|[Am]Lift my eyes now |[F]lift my heart now\n|[C]Teach me faith now |[G]make me brave\n```\n\n```ol:Final-Chorus\n// Up a whole step from C to D\n|[D]Higher than the morning |[A/C#]brighter than the day\n|[Bm]You are always with me |[G]showing me the way\n```\n\n```ol:Outro\n// Voices only\nMorning after morning, Your kindness finds my heart\nMorning after morning, Your love becomes my song\n```\n"
	},
	{
		id: "example9-instrumental-outro",
		fileName: "example9-instrumental-outro.ol.md",
		title: "March of Grace",
		description: "Instrumental outro using valid intro and instrumental directives in 2/2 time.",
		content: "# March of Grace\n\nUse this example to test an instrumental outro with valid intro and instrumental directives in 2/2 time.\n\n```ol:Config\n- Title: March of Grace\n- Artist: Open Lyric Team\n- Copyright: 2026 Open Lyric\n- Key: D\n- Tempo: 96bpm\n- Time: 2/2\n- Structure: IV1CV2B1O\n- Strumming Patterns:\n	// Slow rolling pulse\n	d--u-- | d-u---\n	// Lift on the chorus\n	ddu--- | d-u-u-\n```\n\n```ol:Intro\n{p: #4 } | D | A | Bm | G |\n```\n\n```ol:Verse 1\n[D]You lead us through the battle line\n[A]You keep our courage steady\n  // Snare joins on the third line\n[Bm]You turn the trembling heart to praise\n[G]And make the weary ready\n```\n\n```ol:Chorus\n|[D]Grace goes before us |[A]grace stands beside us\n|[Bm]Grace is the banner |[G]over this field\n```\n\n```ol:Verse 2\nEvery promise keeps its weight when You have spoken\nEvery fear begins to break when hope is woken\n```\n\n```ol:Bridge 1\n// Shout the first line, sing the second\n|[Bm]We will not retreat |[G]We will not be shaken\n|[D]You remain our peace |[A]You remain our song\n```\n\n```ol:Outro\n// Brass takes the melody to the end\n{c: Brass line } | D | A | Bm | G |\n```\n"
	},
	{
		id: "example10-commented-draft",
		fileName: "example10-commented-draft.ol.md",
		title: "Commented Draft Template",
		description: "Comment-heavy drafting template showing ignored // lines in every fence type.",
		content: "# Commented Draft Template\n\nUse this example to test draft comments with ignored `//` lines across config, intro, instrumental, lyric, bridge, note, and outro fences.\n\n```ol:Config\n// Draft template with comments in every fence type.\n- Title: Commented Draft Template\n- Artist: Open Lyric Team\n- Copyright: 2026 Open Lyric\n- Key: A\n- Tempo: 82bpm\n- Time: 4/4\n- Structure: IV1IS1CB1N1O\n- Strumming Patterns:\n	// Slow rolling pulse\n	d--u-- | d-u---\n	// Lift on the chorus\n	ddu--- | d-u-u-\n```\n\n```ol:Intro\n// Pad only for the first pass.\n{p: #1 } | A | E/G# | F#m | D |\n```\n\n```ol:Verse 1\n// Draft this lyric later.\n[A]You are near when daylight fades\n[E/G#]You are near when courage shakes\n```\n\n```ol:Instrumental 1\n// Guitar echoes the chorus motif.\n{c: Gtr Solo } | A | E/G# | F#m | D | (2x)\n```\n\n```ol:Chorus\n// Keep the chorus short on purpose.\n|[A]You are here |[E/G#]You are faithful\n|[F#m]You are near |[D]You are kind\n```\n\n```ol:Bridge 1\n// Add a second line later if needed.\n|[D]All my questions |[E]find their rest in You\n```\n\n```ol:Note 1\n// Spoken over the pads before the outro.\nRest here a moment before the last refrain\n```\n\n```ol:Outro\n// Leave this instrumental while arranging.\n{c: Piano + pads } | A | E/G# | F#m | D |\n```\n\n```ol:Note 2\n// A rehearsal note, listed after the song.\nTry the bridge in half-time next rehearsal\nAsk the keys player for a softer pad\n```\n"
	},
	{
		id: "example11-twelve-eight-and-aliases",
		fileName: "example11-twelve-eight-and-aliases.ol.md",
		title: "Twelve-Eight Lanterns",
		description: "12/8 example using the singular Strumming Pattern alias and chord extensions.",
		content: "# Twelve-Eight Lanterns\n\nUse this example to test 12/8 time, the singular `Strumming Pattern` alias, and extended chord spellings.\n\n```ol:Config\n- Title: Twelve-Eight Lanterns\n- Artist: Open Lyric Team\n- Copyright: 2026 Open Lyric\n- Key: F#m\n- Tempo: 54bpm\n- Time: 12/8\n- Theme: Night prayer\n- Structure: IV1PCV2CB1FO\n- Genre: Worship\n- Style: 12/8 Ballad\n- Strumming Pattern: d--u--d--u- | d-u-u-d-u-u\n```\n\n```ol:Intro\n// Count four big beats per bar\n| F#m | Emaj7 | Dadd9 | C#sus4 |\n```\n\n```ol:Verse 1\nLantern light is trembling, but Your promise stays\nMidnight keeps on breathing, but Your mercy stays\n```\n\n```ol:Pre-Chorus\n// Pull back to just keys\n[Dadd9]Even in the shadow, [Emaj7]You are leading me\n[F#m]Even in the silence, [C#sus4]You are speaking peace\n```\n\n```ol:Chorus\n|[F#m]Hold me through the midnight |[Emaj7]keep my heart awake\n|[Dadd9]Hold me through the midnight |[C#sus4]for Your mercy's sake\n```\n\n```ol:Verse 2\nEvery distant answer glows within Your word\nEvery hidden ember wakes when You are heard\n```\n\n```ol:Bridge 1\n|[Dadd9]Light upon light |[Emaj7]grace upon grace\n|[F#m]Song upon song |[C#sus4]face upon face\n```\n\n```ol:Final-Chorus\n// Up a whole step from F#m to G#m\n|[G#m]Hold me through the midnight |[F#maj7]keep my heart awake\n|[Eadd9]Hold me through the midnight |[D#sus4]for Your mercy's sake\n```\n\n```ol:Outro\nLantern light keeps burning while Your presence stays\n```\n"
	},
	{
		id: "example12-markdown-decorations",
		fileName: "example12-markdown-decorations.ol.md",
		title: "Markdown Decoration Demo",
		description: "Bold, italic, and font color examples rendered directly inside Open Lyric fences.",
		content: "# Markdown Decoration Demo\n\nUse this example to test inline markdown decoration such as bold, italic, and font color inside Open Lyric fences.\n\n```ol:Config\n- Title: Markdown Decoration Demo\n- Subtitle: Styling text inside Open Lyric fences\n- Description:\n	This draft shows **bold**, *italic*, and <font color=\"#0f766e\">color</font> text\n	inside fenced Open Lyric sections while chords still align with lyrics.\n- Artist: Open Lyric Team\n- Copyright: 2026 Open Lyric\n- Key: D\n- Tempo: 74bpm\n- Time: 4/4\n- Theme: Hope-filled worship\n- Structure: IV1CDO\n- Genre: Worship\n- Style: Contemporary\n- Strumming Patterns:\n	// Slow rolling pulse\n	d--u-- | d-u---\n	// Lift on the chorus\n	ddu--- | d-u-u-\n```\n\n```ol:Intro\n| D | A/C# | Bm7 | G |\n```\n\n```ol:Verse 1\n[D]You turn the **darkest** night to [A/C#]*morning*\n[Bm7]You speak in <font color=\"#0f766e\">mercy</font> over [G]me\n```\n\n```ol:Chorus\n// **Not bold**, *not italic*: a comment shows verbatim\n|[D]Sing a **new** song, let the *whole* heart rise\n|[A/C#]Hold to the <font color=\"#2563eb\">promise</font> lighting up the skies\n|[Bm7]Grace is still unfolding, [G]grace is still alive\n```\n\n```ol:Breakdown\n// Read it, don't sing it\nSpeak this softly:\n**You are near**\n*You are faithful*\n<font color=\"#dc2626\">You never let us go</font>\n```\n\n```ol:Outro\n|[D]Stay with me in the *quiet* [G]light\n```\n"
	},
	{
		id: "example13-sung-intro",
		fileName: "example13-sung-intro.ol.md",
		title: "Before the Light",
		description: "Sung Intro: a cue and progression line followed by the lyric that opens the song over it.",
		content: "# Before the Light\n\nUse this example to test a sung `Intro` — a cue and progression line followed by the lyric that opens the song over it. `Intro` and `Outro` are the two mixed sections: each line is read as a progression or as lyrics on its own, so a hook sung cold can sit under the progression that sets it up.\n\n```ol:Config\n- Title: Before the Light\n- Subtitle: A Sung Intro\n- Artist: Open Lyric Team\n- Copyright: 2026 Open Lyric\n- Key: G\n- Tempo: 68bpm\n- Time: 4/4\n- Theme: Waiting on God\n- Structure: IV1CV2CO\n- Strumming Patterns:\n	// Soft eighths under the sung intro\n	d--u-- | d-u---\n	// Full strum from the first verse\n	ddu--- | d-u-u-\n```\n\n```ol:Intro\n// The band waits a bar, then the voice comes in alone over the same figure\n{p: #1 } | G | D/F# | Em7 | Cadd9 | (2x)\nStill You are near, still You are near\nStill You are near when the daylight fades\n```\n\n```ol:Verse 1\nMorning breaks with mercy on the water\nEvery breath reminds me You are here\n```\n\n```ol:Chorus\n|[G]Before the light arrives, You are already good\n|[D/F#]Before I find the words, You have already heard\n|[Em7]Before the light arrives, You are already good\n|[Cadd9]Faithful in the waiting, faithful in the dark\n```\n\n```ol:Verse 2\nEvening folds the hours into stillness\nEvery scattered thought returns to rest\n```\n\n```ol:Outro\n{p: #1 } | G | D/F# | Em7 | Cadd9 |\n[G]Still You are near, [Em7]still You are near\n```\n"
	}
];
//#endregion
//#region src/open-lyric-mcp/operations/reference.ts
function listExamples() {
	return OPEN_LYRIC_EXAMPLES.map(({ id, fileName, title, description }) => ({
		id,
		fileName,
		title,
		description
	}));
}
function getExample(id) {
	const wanted = String(id ?? "").trim().replace(/\.ol\.md$/, "");
	const example = OPEN_LYRIC_EXAMPLES.find((candidate) => candidate.id === wanted || candidate.fileName === `${wanted}.ol.md`);
	if (!example) throw new SongOperationError(`No example "${id}". Examples: ${OPEN_LYRIC_EXAMPLES.map((candidate) => candidate.id).join(", ")}.`);
	return {
		id: example.id,
		fileName: example.fileName,
		title: example.title,
		description: example.description,
		text: example.content
	};
}
function getNotationDocument() {
	return schema_default;
}
/** The reference split at its `## N. Title` headings. */
function listNotationSections() {
	const sections = [];
	const lines = schema_default.split("\n");
	let current = null;
	let fence = "";
	lines.forEach((line) => {
		const fenceMatch = line.match(/^(`{3,})/);
		if (fenceMatch) {
			if (!fence) fence = fenceMatch[1];
			else if (line.trim() === fence) fence = "";
		}
		const headingMatch = fence ? null : line.match(/^## (\d+)\.\s+(.*)$/);
		if (headingMatch) {
			current = {
				id: headingMatch[1],
				title: headingMatch[2].replace(/`/g, "").trim(),
				text: ""
			};
			sections.push(current);
		}
		if (current) current.text += `${line}\n`;
	});
	sections.forEach((section) => {
		section.text = section.text.replace(/\n+(?:---\n*)?$/, "\n");
	});
	return sections;
}
function getNotationSection(idOrTitle) {
	const wanted = String(idOrTitle ?? "").trim().toLowerCase().replace(/^§/, "");
	const sections = listNotationSections();
	const section = sections.find((candidate) => candidate.id === wanted || candidate.title.toLowerCase() === wanted || candidate.title.toLowerCase().includes(wanted));
	if (!wanted || !section) throw new SongOperationError(`No reference section "${idOrTitle}". Sections: ${sections.map((candidate) => `${candidate.id} ${candidate.title}`).join("; ")}.`);
	return section;
}
/** The JSON fence under a `### <heading>` of the reference. */
function readJsonBlockAfterHeading(headingPrefix) {
	const lines = schema_default.split("\n");
	const headingIndex = lines.findIndex((line) => line.startsWith(`### ${headingPrefix}`));
	if (headingIndex < 0) throw new Error(`schema.md has no "### ${headingPrefix}" heading.`);
	for (let index = headingIndex + 1; index < lines.length; index += 1) {
		const open = lines[index].match(/^(`{3,})json\s*$/);
		if (!open) continue;
		const end = lines.findIndex((line, lineIndex) => lineIndex > index && line.trim() === open[1]);
		return lines.slice(index + 1, end).join("\n");
	}
	throw new Error(`schema.md has no JSON block under "### ${headingPrefix}".`);
}
var grammarCache = null;
var songSchemaCache = null;
/** §8.1 — every fence, pattern, enum and diagnostic, as data. */
function getNotationGrammar() {
	grammarCache ??= JSON.parse(readJsonBlockAfterHeading("8.1"));
	return grammarCache;
}
/** §8.2 — the JSON Schema (draft 2020-12) of a song object. */
function getSongJsonSchema() {
	songSchemaCache ??= JSON.parse(readJsonBlockAfterHeading("8.2"));
	return songSchemaCache;
}
function listFenceTypes() {
	const grammar = getNotationGrammar();
	const bodyRules = new Map((grammar.fences ?? []).map((fence) => [fence.header, fence.bodyRule]));
	const structureCodes = new Map(STRUCTURE_TOKEN_DEFINITIONS.map((definition) => [definition.header, definition.code]));
	return registry.getDefinitions().map((definition) => {
		const bodyRule = bodyRules.get(definition.header) ?? "";
		return {
			header: definition.header,
			kind: definition.kind,
			description: definition.description || "",
			numbered: Boolean(definition.allowsNumbering),
			required: Boolean(definition.required),
			allowsDuplicates: Boolean(definition.allowsDuplicateDeclaredPart?.()),
			structureCode: structureCodes.get(definition.header) ?? null,
			bodyRule,
			bodyRuleDescription: grammar.bodyRules?.[bodyRule]?.description ?? "",
			example: `\`\`\`ol:${definition.header}${definition.allowsNumbering ? " 1" : ""}`
		};
	});
}
var CONFIG_FIELD_NOTES = {
	Title: "The song title.",
	Subtitle: "A second title line.",
	Description: "Free text; continuation lines are indented under the field line.",
	Artist: "Performer or writer credit.",
	Copyright: "Copyright / licensing line.",
	Locales: "Comma-separated language tags from a closed set (en-US, km-KH, fr-FR …).",
	Key: "The song key; transposition and chord suggestions read it.",
	Tempo: "Beats per minute, written like 68bpm.",
	Time: "Time signature.",
	Theme: "A free-text theme or topic.",
	Structure: `The performance order in compact codes, e.g. ${STRUCTURE_SYNTAX_EXAMPLE}.`,
	Genre: "Free text.",
	Style: "Free text.",
	Keywords: "Comma-separated search keywords, free text.",
	Year: "The year the song was written or released, four digits like 2024.",
	Melody: "The tune the lyrics are sung to, such as the name of an existing melody; free text.",
	Attachments: "One link per line (YouTube, audio, video, PDF, image …), optionally [label](url).",
	"Strumming Patterns": "One pattern per indented line, each optionally labelled by a // comment line above it; {p: #N} selects the Nth."
};
function listConfigFields() {
	const aliasesByField = /* @__PURE__ */ new Map();
	Object.entries(CONFIG_FIELD_ALIASES).forEach(([alias, field]) => {
		aliasesByField.set(field, [...aliasesByField.get(field) ?? [], alias]);
	});
	return CONFIG_FIELD_NAMES$1.map((name) => {
		const info = {
			name,
			required: CONFIG_REQUIRED_FIELD_NAMES$1.includes(name),
			multiline: CONFIG_MULTILINE_FIELD_NAMES$1.includes(name),
			aliases: aliasesByField.get(name) ?? [],
			note: CONFIG_FIELD_NOTES[name] ?? ""
		};
		const enumValues = CONFIG_ENUM_FIELD_VALUES$1[name];
		if (enumValues) info.values = [...enumValues];
		const valuePattern = CONFIG_PATTERN_FIELD_VALUES$1[name];
		if (valuePattern) info.pattern = valuePattern.source;
		if (name === "Locales") info.values = [...CONFIG_LOCALE_VALUES];
		return info;
	});
}
function listKeys() {
	return [...CONFIG_KEY_VALUES];
}
function listStructureCodes() {
	return STRUCTURE_TOKEN_DEFINITIONS.map((definition) => ({
		code: definition.code,
		header: definition.header,
		numbered: Boolean(definition.allowsNumbering)
	}));
}
//#endregion
//#region src/open-lyric-mcp/resources.ts
/**
* Read-only reference material as MCP resources: the notation reference
* (whole and by section), its two JSON schemas, the example songs, and the
* fence / Config tables.
*/
function jsonContents(uri, value) {
	return { contents: [{
		uri: uri.href,
		mimeType: "application/json",
		text: `${JSON.stringify(value, null, 2)}\n`
	}] };
}
function markdownContents(uri, text) {
	return { contents: [{
		uri: uri.href,
		mimeType: "text/markdown",
		text
	}] };
}
function registerOpenLyricResources(server) {
	server.registerResource("notation-reference", "open-lyric://docs/notation", {
		title: "Open Lyric notation reference",
		description: "The whole notation: fences, sections, inline syntax, Config, Structure, every diagnostic, a complete example, and the machine-readable schemas. Read before writing a song.",
		mimeType: "text/markdown"
	}, (uri) => markdownContents(uri, getNotationDocument()));
	server.registerResource("notation-reference-section", new ResourceTemplate("open-lyric://docs/notation/{section}", {
		list: () => ({ resources: listNotationSections().map((section) => ({
			uri: `open-lyric://docs/notation/${section.id}`,
			name: `notation-${section.id}`,
			title: `${section.id}. ${section.title}`,
			mimeType: "text/markdown"
		})) }),
		complete: { section: (value) => listNotationSections().map((section) => section.id).filter((id) => id.startsWith(value)) }
	}), {
		title: "Notation reference section",
		description: "One numbered section of the notation reference.",
		mimeType: "text/markdown"
	}, (uri, { section }) => markdownContents(uri, getNotationSection(String(section)).text));
	server.registerResource("notation-grammar", "open-lyric://schema/grammar.json", {
		title: "Open Lyric grammar (JSON)",
		description: "Every fence, pattern, enum and diagnostic of the notation, as data (reference §8.1).",
		mimeType: "application/json"
	}, (uri) => jsonContents(uri, getNotationGrammar()));
	server.registerResource("song-schema", "open-lyric://schema/song.schema.json", {
		title: "Open Lyric song object schema",
		description: "JSON Schema (draft 2020-12) of a song as { config, sections } — what parse_song returns and song_from_json takes (reference §8.2).",
		mimeType: "application/schema+json"
	}, (uri) => jsonContents(uri, getSongJsonSchema()));
	server.registerResource("examples", "open-lyric://examples", {
		title: "Example songs",
		description: "The bundled example songs: id, file name, title, description.",
		mimeType: "application/json"
	}, (uri) => jsonContents(uri, listExamples()));
	server.registerResource("example", new ResourceTemplate("open-lyric://examples/{id}", {
		list: () => ({ resources: listExamples().map((example) => ({
			uri: `open-lyric://examples/${example.id}`,
			name: example.fileName,
			title: example.title,
			description: example.description,
			mimeType: "text/markdown"
		})) }),
		complete: { id: (value) => listExamples().map((example) => example.id).filter((id) => id.startsWith(value)) }
	}), {
		title: "Example song",
		description: "One bundled example song, as notation.",
		mimeType: "text/markdown"
	}, (uri, { id }) => markdownContents(uri, getExample(String(id)).text));
	server.registerResource("fence-types", "open-lyric://reference/fences", {
		title: "Section types",
		description: "Every ol: fence type with its Structure code and body rule.",
		mimeType: "application/json"
	}, (uri) => jsonContents(uri, listFenceTypes()));
	server.registerResource("config-fields", "open-lyric://reference/config-fields", {
		title: "Config fields",
		description: "Every ol:Config field with its rules and value sets.",
		mimeType: "application/json"
	}, (uri) => jsonContents(uri, listConfigFields()));
}
//#endregion
//#region src/open-lyric-mcp/schemas.ts
/** The zod pieces the Open Lyric MCP tools share. */
var KEY_VALUES = CONFIG_KEY_VALUES;
var TIME_VALUES = CONFIG_ENUM_FIELD_VALUES$1.Time;
var SECTION_HEADERS = STRUCTURE_TOKEN_DEFINITIONS.map((definition) => definition.header);
var keySchema = z.enum(KEY_VALUES).describe("A key as Config writes it: C, Db … B, Am … G#m.");
var songSourceShape = {
	text: z.string().optional().describe("The song as Open Lyric notation (Markdown with ```ol: fences)."),
	path: z.string().optional().describe("Instead of text: a song file (.ol.md) inside the allowed roots; relative paths resolve against the first root.")
};
var editShape = {
	...songSourceShape,
	dryRun: z.boolean().optional().describe("With path: return the edited text without writing the file. (With text the edited text is always returned and nothing is written.)")
};
var viewOptionsShape = {
	key: keySchema.optional().describe("Show the song in this key (needs a Config Key of the same mode)."),
	simplifyChords: z.boolean().optional().describe("Show chords as plain triads (Cmaj7 → C)."),
	hideChords: z.boolean().optional().describe("Lyrics only. The pptx and slideshow decks are lyrics only unless this is false."),
	hideLeadingBars: z.boolean().optional().describe("Drop the | bar marks that open lyric lines."),
	hideStrummingPatterns: z.boolean().optional(),
	hideAttachments: z.boolean().optional(),
	showComments: z.boolean().optional().describe("Show // comment lines."),
	hideNotes: z.boolean().optional().describe("Leave out the ol:Note sections the Structure does not list (shown after the song by default)."),
	section: z.string().optional().describe("Lyric view and text only: just this part, e.g. \"Chorus\" or \"Verse 2\".")
};
var diagnosticSchema = z.object({
	message: z.string(),
	severity: z.enum([
		"error",
		"warning",
		"information",
		"hint"
	]),
	line: z.number().describe("1-based."),
	column: z.number().describe("1-based."),
	endLine: z.number(),
	endColumn: z.number().describe("1-based, just past the last character."),
	fix: z.object({
		title: z.string(),
		text: z.string()
	}).optional().describe("The fix, when the validator knows it: put `text` in place of line:column–endLine:endColumn (e.g. \"Verse 2\" for a fence header written \"Vers 2\").")
});
var validationSchema = z.object({
	valid: z.boolean().describe("No errors (warnings allowed)."),
	errorCount: z.number(),
	warningCount: z.number(),
	diagnostics: z.array(diagnosticSchema)
});
/** What every edit tool returns, plus its own fields. */
var editOutputShape = {
	text: z.string().optional().describe("The edited song — returned for text input, dry runs and read-only servers."),
	path: z.string().optional().describe("The file edited, for path input."),
	written: z.boolean().describe("Whether the file was written."),
	validation: validationSchema,
	note: z.string().optional()
};
var strummingPatternSchema = z.object({
	label: z.string().optional().describe("Written above the pattern as a // comment line."),
	pattern: z.string().describe("e.g. \"d--u-- | d-u---\".")
});
var configValueSchema = z.union([
	z.string(),
	z.array(z.string()),
	z.array(strummingPatternSchema),
	z.null()
]).describe("A string; a list for Description, Attachments, Locales and Keywords (one entry per line / tag / keyword); a list of { label?, pattern } for Strumming Patterns; empty or null to remove the field.");
var sectionHeaderSchema = z.enum(SECTION_HEADERS).describe("The section type — spelling is exact.");
var songSectionSchema = z.object({
	header: sectionHeaderSchema,
	index: z.number().int().min(1).optional().describe("Makes the part name \"<header> <index>\"; only for numbered types."),
	lines: z.array(z.string()).describe("The fence body, one entry per line: lyric lines with [Chord] annotations, progressions, // comments, indented translation lines.")
});
var songConfigSchema = z.object({
	Title: z.string().min(1),
	Structure: z.string().describe("Compact performance order, e.g. IV1CV2CBCO (see explain_structure)."),
	Subtitle: z.string().optional(),
	Description: z.array(z.string()).optional(),
	Artist: z.string().optional(),
	Copyright: z.string().optional(),
	Locales: z.array(z.string()).optional().describe("Tags like en-US, km-KH."),
	Key: keySchema.optional(),
	Tempo: z.string().optional().describe("e.g. 72bpm"),
	Time: z.enum(TIME_VALUES).optional(),
	Theme: z.string().optional(),
	Genre: z.string().optional(),
	Style: z.string().optional(),
	Keywords: z.array(z.string()).optional().describe("Serialized as one comma-separated line."),
	Year: z.string().optional().describe("Four digits, e.g. 2024."),
	Melody: z.string().optional().describe("The tune the lyrics are sung to."),
	Attachments: z.array(z.string()).optional(),
	"Strumming Patterns": z.array(strummingPatternSchema).optional()
});
var songObjectSchema = z.object({
	config: songConfigSchema,
	sections: z.array(songSectionSchema).min(1)
});
//#endregion
//#region src/open-lyric-mcp/tools/analysis.ts
var READ_ONLY$2 = {
	readOnlyHint: true,
	openWorldHint: false
};
var structureStepSchema = z.object({
	code: z.string(),
	partName: z.string(),
	repeat: z.number(),
	label: z.string(),
	declared: z.boolean().optional()
});
var structureSchema = z.object({
	text: z.string(),
	error: z.string().nullable(),
	steps: z.array(structureStepSchema),
	undeclaredParts: z.array(z.string()),
	unusedSections: z.array(z.string())
});
var sectionSchema = z.object({
	partName: z.string(),
	header: z.string(),
	index: z.number().optional(),
	kind: z.string(),
	startLine: z.number(),
	endLine: z.number(),
	lineCount: z.number(),
	inStructure: z.boolean()
});
function registerAnalysisTools({ server, files }) {
	server.registerTool("validate_song", {
		title: "Validate a song",
		description: "Check a song against the Open Lyric rules with the editor's own validator. Returns every diagnostic with 1-based line/column. Run it after every edit.",
		inputSchema: songSourceShape,
		outputSchema: validationSchema.shape,
		annotations: READ_ONLY$2
	}, (args) => runTool(async () => {
		const validation = validateSong((await readSongSource(files, args)).text);
		return structuredResult(validation, summarizeValidation(validation));
	}));
	server.registerTool("parse_song", {
		title: "Parse a song into a song object",
		description: "The song as a structured object — { config, sections } per the song schema (open-lyric://schema/song.schema.json) — plus the Markdown preamble outside the fences and anything the object cannot carry (comments in Config, unknown fields).",
		inputSchema: songSourceShape,
		outputSchema: {
			song: z.looseObject({}).describe("The song object."),
			preamble: z.string(),
			warnings: z.array(z.string())
		},
		annotations: READ_ONLY$2
	}, (args) => runTool(async () => {
		const { song, preamble, warnings } = songObjectFromMarkdown((await readSongSource(files, args)).text);
		return structuredResult({
			song,
			preamble,
			warnings
		});
	}));
	server.registerTool("get_song_info", {
		title: "Summarize a song",
		description: "Title and metadata, the structure step by step (with undeclared and unused parts), the sections, every chord, attachments and strumming patterns.",
		inputSchema: songSourceShape,
		outputSchema: {
			hasConfig: z.boolean(),
			title: z.string(),
			subtitle: z.string().optional(),
			artist: z.string().optional(),
			copyright: z.string().optional(),
			description: z.array(z.string()),
			locales: z.array(z.string()),
			key: z.string().optional(),
			tempo: z.string().optional(),
			time: z.string().optional(),
			theme: z.string().optional(),
			genre: z.string().optional(),
			style: z.string().optional(),
			keywords: z.array(z.string()),
			year: z.string().optional(),
			melody: z.string().optional(),
			structure: structureSchema,
			sections: z.array(sectionSchema),
			chords: z.array(z.string()),
			attachments: z.array(z.object({
				title: z.string(),
				type: z.string(),
				link: z.string()
			})),
			strummingPatterns: z.array(z.object({
				label: z.string().optional(),
				pattern: z.string()
			})),
			warnings: z.array(z.string())
		},
		annotations: READ_ONLY$2
	}, (args) => runTool(async () => {
		const info = getSongInfo((await readSongSource(files, args)).text);
		return structuredResult(info, `${info.title || "Untitled"} — ${info.sections.length} section(s), structure ${info.structure.text || "(none)"}.`);
	}));
	server.registerTool("list_sections", {
		title: "List the sections",
		description: "Every section fence in written order: part name, type, line range, and whether Structure plays it.",
		inputSchema: songSourceShape,
		outputSchema: { sections: z.array(sectionSchema) },
		annotations: READ_ONLY$2
	}, (args) => runTool(async () => {
		const sections = listSongSections((await readSongSource(files, args)).text);
		return structuredResult({ sections }, sections.map((section) => section.partName).join(", ") || "No sections.");
	}));
	server.registerTool("get_section", {
		title: "Read one section's lines",
		description: "The body lines of one section, as written, with its line range.",
		inputSchema: {
			...songSourceShape,
			section: z.string().describe("The part name, e.g. \"Chorus\" or \"Verse 2\".")
		},
		outputSchema: {
			partName: z.string(),
			header: z.string(),
			lines: z.array(z.string()),
			startLine: z.number(),
			endLine: z.number()
		},
		annotations: READ_ONLY$2
	}, ({ section, ...args }) => runTool(async () => {
		return structuredResult(getSectionLines((await readSongSource(files, args)).text, section));
	}));
	server.registerTool("explain_structure", {
		title: "Explain a Structure value",
		description: "Read a compact Structure value (e.g. IV1x2CV2CBCx2O) step by step: part, repeat count, and — given the song — which parts no section declares and which sections are never played.",
		inputSchema: {
			structure: z.string().optional().describe("The Structure value. Default: the song's own."),
			...songSourceShape
		},
		outputSchema: structureSchema.shape,
		annotations: READ_ONLY$2
	}, ({ structure, ...args }) => runTool(async () => {
		const source = typeof args.text === "string" || Boolean(args.path) ? await readSongSource(files, args) : null;
		const info = describeStructure(structure ?? (source ? songObjectFromMarkdown(source.text).song.config.Structure : ""), source ? listSongSections(source.text).map((section) => section.partName) : void 0);
		return structuredResult(info, info.error ? `Structure error: ${info.error}` : info.steps.map((step) => step.label).join(" → ") || "Empty structure.");
	}));
	server.registerTool("list_chords", {
		title: "List the chords",
		description: "Every distinct chord in the song, with its name, simplified triad, degree hints, and whether it is diatonic to the song's key.",
		inputSchema: songSourceShape,
		outputSchema: {
			key: z.string(),
			diatonicTriads: z.array(z.string()),
			chords: z.array(z.object({
				chord: z.string(),
				name: z.string(),
				simplified: z.string(),
				degreeHints: z.array(z.string()),
				inKey: z.boolean().optional()
			}))
		},
		annotations: READ_ONLY$2
	}, (args) => runTool(async () => {
		const chords = listSongChords((await readSongSource(files, args)).text);
		return structuredResult(chords, chords.chords.map((chord) => chord.chord).join(" ") || "No chords.");
	}));
}
//#endregion
//#region src/open-lyric-mcp/tools/editing.ts
var newSongShape = {
	path: z.string().optional().describe("Write the new song to this file (.ol.md) instead of returning it."),
	overwrite: z.boolean().optional().describe("Replace the file at path if it exists. Default false.")
};
var newSongOutputShape = {
	text: z.string().optional().describe("The new song, when no path was given."),
	path: z.string().optional(),
	written: z.boolean(),
	validation: editOutputShape.validation
};
var EDIT = {
	readOnlyHint: false,
	destructiveHint: true,
	openWorldHint: false
};
function registerEditingTools({ server, files }) {
	server.registerTool("create_song", {
		title: "Create a song",
		description: "Write a new, valid Open Lyric song from its fields and sections. Structure defaults to every section once, in order. Returns the notation, or writes it to path.",
		inputSchema: {
			title: z.string().min(1),
			subtitle: z.string().optional(),
			description: z.array(z.string()).optional().describe("One entry per line."),
			artist: z.string().optional(),
			copyright: z.string().optional(),
			locales: z.array(z.string()).optional().describe("Tags like en-US, km-KH."),
			key: keySchema.optional(),
			tempo: z.union([z.number().int().positive(), z.string()]).optional().describe("72 or \"72bpm\"."),
			time: z.string().optional().describe("4/4, 3/4, 6/8 …"),
			theme: z.string().optional(),
			genre: z.string().optional(),
			style: z.string().optional(),
			keywords: z.array(z.string()).optional().describe("Search keywords; written as one comma-separated line."),
			year: z.union([z.number().int().min(1e3).max(9999), z.string()]).optional().describe("2024 or \"2024\"."),
			melody: z.string().optional().describe("The tune the lyrics are sung to."),
			attachments: z.array(z.string()).optional().describe("URLs or [label](url)."),
			strummingPatterns: z.array(strummingPatternSchema).optional(),
			structure: z.string().optional().describe("Compact order like IV1CV2CBCO. Default: derived from sections."),
			sections: z.array(z.object({
				header: sectionHeaderSchema,
				index: z.number().int().min(1).optional(),
				lines: z.array(z.string()).optional()
			})).optional().describe("In written order. Default: one empty Verse 1."),
			preamble: z.string().optional().describe("Markdown above the fences. Default \"# <title>\"."),
			...newSongShape
		},
		outputSchema: newSongOutputShape,
		annotations: {
			...EDIT,
			destructiveHint: false,
			idempotentHint: true
		}
	}, ({ path, overwrite, ...input }) => runTool(async () => {
		return finishNewSong(files, createSong(input), {
			path,
			overwrite,
			summary: `Created "${input.title}".`
		});
	}));
	server.registerTool("song_from_json", {
		title: "Serialize a song object",
		description: "Turn a song object ({ config, sections } — open-lyric://schema/song.schema.json) into Open Lyric notation and validate it. The schema checks shapes; the result validation checks everything else.",
		inputSchema: {
			song: songObjectSchema,
			preamble: z.string().optional().describe("Markdown above the fences."),
			...newSongShape
		},
		outputSchema: newSongOutputShape,
		annotations: {
			...EDIT,
			destructiveHint: false,
			idempotentHint: true
		}
	}, ({ song, preamble, path, overwrite }) => runTool(async () => finishNewSong(files, songFromObject(song, { preamble }), {
		path,
		overwrite,
		summary: `Serialized "${song.config.Title}".`
	})));
	server.registerTool("import_plain_text", {
		title: "Import plain text",
		description: "Convert a plain-text song in Open Lyric's text layout — title and artist lines, a 'Key: G, Tempo: 68bpm, Time: 4/4' line, 'Section:' headings with indented lines, chords above lyrics — into notation, the way the editor's paste import does. Labels from other formats (Ending, Middle 8, Hook …) become Open Lyric sections; missing fields get placeholders. For other chord-sheet layouts, write the song yourself (see create_song).",
		inputSchema: {
			plainText: z.string(),
			...newSongShape
		},
		outputSchema: {
			...newSongOutputShape,
			matchesPlainTextFormat: z.boolean(),
			renamedSections: z.array(z.object({
				from: z.string(),
				to: z.string()
			})),
			placeholdersUsed: z.boolean(),
			hasConflictingDuplicates: z.boolean()
		},
		annotations: {
			...EDIT,
			destructiveHint: false,
			idempotentHint: true
		}
	}, ({ plainText, path, overwrite }) => runTool(async () => {
		const result = importPlainText(plainText);
		return finishNewSong(files, result, {
			path,
			overwrite,
			summary: result.matchesPlainTextFormat ? "Imported the plain text." : "The text did not look like the plain-text layout; the result is a best effort — review it."
		});
	}));
	server.registerTool("set_config_field", {
		title: "Set a Config field",
		description: "Set, replace or remove (empty value) one ol:Config field. A new field is inserted in canonical order. Title and Structure cannot be removed.",
		inputSchema: {
			...editShape,
			field: z.string().describe("Title, Subtitle, Description, Artist, Copyright, Locales, Key, Tempo, Time, Theme, Structure, Genre, Style, Keywords, Year, Melody, Attachments or Strumming Patterns."),
			value: configValueSchema
		},
		outputSchema: {
			...editOutputShape,
			field: z.string(),
			action: z.enum([
				"set",
				"added",
				"removed",
				"unchanged"
			])
		},
		annotations: {
			...EDIT,
			idempotentHint: true
		}
	}, ({ field, value, dryRun, ...args }) => runTool(async () => {
		const source = await readSongSource(files, args);
		const result = setConfigField(source.text, field, value);
		return finishSongEdit(files, source, result, {
			dryRun,
			summary: `${result.field}: ${result.action}.`
		});
	}));
	server.registerTool("add_section", {
		title: "Add a section",
		description: "Add a section fence after the last one — numbered types get the next free number unless index is given — and append its code to Structure (appendToStructure: false to skip).",
		inputSchema: {
			...editShape,
			header: sectionHeaderSchema,
			index: z.number().int().min(1).optional(),
			lines: z.array(z.string()).optional().describe("The body lines."),
			appendToStructure: z.boolean().optional()
		},
		outputSchema: {
			...editOutputShape,
			partName: z.string()
		},
		annotations: {
			...EDIT,
			idempotentHint: false
		}
	}, ({ header, index, lines, appendToStructure, dryRun, ...args }) => runTool(async () => {
		const source = await readSongSource(files, args);
		const result = addSection(source.text, {
			header,
			index,
			lines,
			appendToStructure
		});
		return finishSongEdit(files, source, result, {
			dryRun,
			summary: `Added ${result.partName}.`
		});
	}));
	server.registerTool("rename_section", {
		title: "Rename a section",
		description: "Rename (or renumber, or retype) a section and rewrite every Structure step that plays it.",
		inputSchema: {
			...editShape,
			section: z.string().describe("Current part name, e.g. \"Verse 2\"."),
			newName: z.string().describe("New part name, e.g. \"Verse 3\" or \"Bridge\".")
		},
		outputSchema: {
			...editOutputShape,
			partName: z.string(),
			structureStepsUpdated: z.number()
		},
		annotations: {
			...EDIT,
			idempotentHint: false
		}
	}, ({ section, newName, dryRun, ...args }) => runTool(async () => {
		const source = await readSongSource(files, args);
		const result = renameSection(source.text, section, newName);
		return finishSongEdit(files, source, result, {
			dryRun,
			summary: `Renamed ${section} → ${result.partName} (${result.structureStepsUpdated} structure step(s)).`
		});
	}));
	server.registerTool("delete_section", {
		title: "Delete a section",
		description: "Remove a section fence and every Structure step that plays it.",
		inputSchema: {
			...editShape,
			section: z.string().describe("The part name.")
		},
		outputSchema: {
			...editOutputShape,
			structureStepsRemoved: z.number()
		},
		annotations: {
			...EDIT,
			idempotentHint: true
		}
	}, ({ section, dryRun, ...args }) => runTool(async () => {
		const source = await readSongSource(files, args);
		const result = deleteSection(source.text, section);
		return finishSongEdit(files, source, result, {
			dryRun,
			summary: `Deleted ${section} (${result.structureStepsRemoved} structure step(s)).`
		});
	}));
	server.registerTool("set_section_lines", {
		title: "Replace a section's lines",
		description: "Replace the whole body of one section — lyric lines with [Chord] annotations, progressions, // comments, indented translation lines.",
		inputSchema: {
			...editShape,
			section: z.string().describe("The part name."),
			lines: z.array(z.string())
		},
		outputSchema: {
			...editOutputShape,
			partName: z.string()
		},
		annotations: {
			...EDIT,
			idempotentHint: true
		}
	}, ({ section, lines, dryRun, ...args }) => runTool(async () => {
		const source = await readSongSource(files, args);
		const result = setSectionLines(source.text, section, lines);
		return finishSongEdit(files, source, result, {
			dryRun,
			summary: `Replaced the lines of ${result.partName}.`
		});
	}));
	server.registerTool("format_song", {
		title: "Format a song",
		description: "The editor's Format Document as it runs with no language plugin: collapse repeated invisible characters and trim trailing whitespace on every line. A language's word-separator repair comes from its plugin in the editor, and none runs here — for Khmer (the km-KH plugin turns a space typed between Khmer letters into U+200B) use khmer-lint's fix_khmer with rules ['word-separator']; a song whose Locales include Khmer gets a hint saying so.",
		inputSchema: editShape,
		outputSchema: {
			...editOutputShape,
			changedLines: z.number(),
			hint: z.string().optional().describe("Present when the song declares a language whose editor Format does more than this server can.")
		},
		annotations: {
			...EDIT,
			idempotentHint: true
		}
	}, ({ dryRun, ...args }) => runTool(async () => {
		const source = await readSongSource(files, args);
		const result = formatSong(source.text);
		const summary = `Formatted: ${result.changedLines} line(s) changed.`;
		return finishSongEdit(files, source, result, {
			dryRun,
			summary: result.hint ? `${summary}\n${result.hint}` : summary
		});
	}));
	server.registerTool("apply_fixes", {
		title: "Apply the known fixes",
		description: "Apply every fix validate_song reports — the diagnostics that carry fix: { title, text }, the editor's quick fixes: a near-miss fence header (ol:Vers 2 → ol:Verse 2), a Config field name or value (Key: g → G, Tempo: 76 bpm → 76bpm), a chord annotation ([Gzz] → [G]), a repeat mark — then validate again until none is left. Returns what was applied; diagnostics with no known fix stay in validation, for the editing tools.",
		inputSchema: editShape,
		outputSchema: {
			...editOutputShape,
			applied: z.array(z.object({
				message: z.string().describe("The diagnostic it answered."),
				title: z.string().describe("What it did."),
				line: z.number().describe("1-based line of the fixed range, in the text as it was then."),
				column: z.number()
			})).describe("The fixes made, in song order within each pass.")
		},
		annotations: {
			...EDIT,
			idempotentHint: true
		}
	}, ({ dryRun, ...args }) => runTool(async () => {
		const source = await readSongSource(files, args);
		const result = applyFixes(source.text);
		return finishSongEdit(files, source, result, {
			dryRun,
			summary: result.applied.length ? [`Applied ${result.applied.length} fix(es):`, ...result.applied.map((fix) => `- line ${fix.line}: ${fix.title}`)].join("\n") : "No diagnostic has a known fix."
		});
	}));
}
//#endregion
//#region src/open-lyric-mcp/tools/files.ts
function registerFileTools({ server, files }, { readOnly }) {
	server.registerTool("list_songs", {
		title: "List song files",
		description: "Find Open Lyric song files (*.ol.md) under the allowed roots (or one folder inside them). Skips dot-folders, node_modules and dist.",
		inputSchema: {
			directory: z.string().optional().describe("A folder inside the roots. Default: every root."),
			recursive: z.boolean().optional().describe("Default true."),
			includeAllMarkdown: z.boolean().optional().describe("List every .md file, not just .ol.md.")
		},
		outputSchema: {
			roots: z.array(z.string()),
			files: z.array(z.string()),
			truncated: z.boolean()
		},
		annotations: {
			readOnlyHint: true,
			openWorldHint: false
		}
	}, ({ directory, recursive, includeAllMarkdown }) => runTool(async () => {
		const roots = await files.getRoots();
		const result = await files.listFiles({
			directory,
			recursive,
			extensions: includeAllMarkdown ? [".md"] : [".ol.md"]
		});
		return structuredResult({
			roots,
			...result
		}, result.files.length ? `${result.files.length} file(s)${result.truncated ? " (truncated)" : ""}.` : `No song files under ${roots.join(", ")}.`);
	}));
	server.registerTool("read_song", {
		title: "Read a song file",
		description: "Read a song file inside the allowed roots, with its validation.",
		inputSchema: { path: z.string() },
		outputSchema: {
			path: z.string(),
			text: z.string(),
			validation: validationSchema
		},
		annotations: {
			readOnlyHint: true,
			openWorldHint: false
		}
	}, ({ path }) => runTool(async () => {
		const file = await files.readText(path);
		const validation = validateSong(file.text);
		return structuredResult({
			path: file.path,
			text: file.text,
			validation
		}, summarizeValidation(validation));
	}));
	if (readOnly) return;
	server.registerTool("write_song", {
		title: "Write a song file",
		description: "Validate a song and write it to a .md / .ol.md file inside the allowed roots. An invalid song is refused unless allowInvalid; an existing file is replaced only with overwrite.",
		inputSchema: {
			path: z.string(),
			text: z.string(),
			overwrite: z.boolean().optional().describe("Replace an existing file. Default false."),
			allowInvalid: z.boolean().optional().describe("Write even when validation finds errors. Default false.")
		},
		outputSchema: {
			path: z.string(),
			written: z.boolean(),
			bytes: z.number(),
			validation: validationSchema
		},
		annotations: {
			readOnlyHint: false,
			destructiveHint: true,
			idempotentHint: true,
			openWorldHint: false
		}
	}, ({ path, text, overwrite = false, allowInvalid = false }) => runTool(async () => {
		const validation = validateSong(text);
		if (!validation.valid && !allowInvalid) throw new SongOperationError(`Not written — the song has errors (pass allowInvalid: true to write anyway).\n${summarizeValidation(validation)}`);
		const target = await files.resolveForWrite(path, SONG_FILE_EXTENSIONS);
		if (await files.resolveForRead(target).then(() => true, () => false) && !overwrite) throw new SongOperationError(`${target} already exists — pass overwrite: true to replace it.`);
		const written = await files.writeFile(target, text, SONG_FILE_EXTENSIONS);
		return structuredResult({
			path: written.path,
			written: true,
			bytes: written.bytes,
			validation
		}, `Wrote ${written.path}.\n${summarizeValidation(validation)}`);
	}));
}
//#endregion
//#region src/plugins/OpenLyric/domain/chord-voicings.ts
function getStringCount(position) {
	return Array.isArray(position?.frets) ? position.frets.length : 6;
}
function getLowestPitchClass(position) {
	if (!Array.isArray(position?.midi) || !position.midi.length) return null;
	return (position.midi[0] % 12 + 12) % 12;
}
/** Lower is easier: low on the neck, few barres, a small span, open strings. */
function scorePosition(position) {
	const frets = Array.isArray(position?.frets) ? position.frets : [];
	const openStringCount = frets.filter((fret) => fret === 0).length;
	const mutedStringCount = frets.filter((fret) => fret < 0).length;
	const frettedNotes = frets.filter((fret) => fret > 0);
	const fretSpan = frettedNotes.length ? Math.max(...frettedNotes) - Math.min(...frettedNotes) : 0;
	return Math.max((position.baseFret || 1) - 1, 0) * 12 + (Array.isArray(position?.barres) ? position.barres.length : 0) * 3 + fretSpan * 2 + frettedNotes.length + mutedStringCount * .5 - openStringCount * 1.5;
}
/**
* Easiest first; with a slash chord's bass pitch class, positions whose lowest
* note is that bass come first.
*/
function rankChordPositions(positions, bassPitchClass) {
	if (!Array.isArray(positions) || !positions.length) return [];
	return positions.map((position, index) => ({
		bassMatches: typeof bassPitchClass === "number" ? getLowestPitchClass(position) === bassPitchClass : false,
		index,
		position,
		score: scorePosition(position)
	})).sort((left, right) => {
		if (left.bassMatches !== right.bassMatches) return Number(right.bassMatches) - Number(left.bassMatches);
		if (left.score !== right.score) return left.score - right.score;
		return left.index - right.index;
	}).map((entry) => entry.position);
}
function deriveBarres(position) {
	const frets = Array.isArray(position?.frets) ? position.frets : [];
	const fingers = Array.isArray(position?.fingers) ? position.fingers : [];
	const barres = Array.isArray(position?.barres) ? position.barres : [];
	const stringCount = getStringCount(position);
	return barres.map((barreFret) => {
		const matchingEntries = frets.map((fret, index) => ({
			fret,
			index,
			finger: fingers[index] || 0
		})).filter((entry) => entry.fret === barreFret);
		if (!matchingEntries.length) return null;
		const targetFinger = matchingEntries.find((entry) => entry.finger > 0)?.finger || 0;
		const filteredEntries = targetFinger ? matchingEntries.filter((entry) => entry.finger === targetFinger) : matchingEntries;
		const fromIndex = filteredEntries[0]?.index;
		const toIndex = filteredEntries[filteredEntries.length - 1]?.index;
		if (typeof fromIndex !== "number" || typeof toIndex !== "number" || fromIndex === toIndex) return null;
		const barreFinger = targetFinger > 0 ? String(targetFinger) : void 0;
		return {
			fromString: stringCount - fromIndex,
			toString: stringCount - toIndex,
			fret: barreFret,
			style: "arc",
			text: barreFinger
		};
	}).filter((barre) => barre !== null);
}
/** SVGuitar's `{ fingers, barres, position }` for a position. */
function createSvguitarData(position) {
	const fingers = [];
	const stringCount = getStringCount(position);
	for (const [index, fret] of (position?.frets || []).entries()) {
		const stringNumber = stringCount - index;
		const fingerNumber = position?.fingers?.[index] || 0;
		if (fret < 0) {
			fingers.push([stringNumber, "x"]);
			continue;
		}
		if (fret === 0) {
			fingers.push([stringNumber, 0]);
			continue;
		}
		fingers.push([
			stringNumber,
			fret,
			fingerNumber > 0 ? String(fingerNumber) : void 0
		]);
	}
	return {
		fingers,
		position: Math.max(position?.baseFret || 1, 1),
		barres: deriveBarres(position)
	};
}
/**
* The database entry for the first suffix candidate it has. By default a chord
* it has no suffix for falls back to the plain major entry (what the editor's
* popup shows); `allowMajorFallback: false` returns `null` instead.
*/
function resolveMatchingChordEntry(database, search, { allowMajorFallback = true } = {}) {
	const chordEntries = database?.chords?.[search.datasetRoot];
	if (!Array.isArray(chordEntries) || !chordEntries.length) return null;
	for (const suffixCandidate of search.suffixCandidates) {
		const matchingEntry = chordEntries.find((entry) => entry.suffix === suffixCandidate);
		if (matchingEntry) return matchingEntry;
	}
	return allowMajorFallback ? chordEntries.find((entry) => entry.suffix === "major") || null : null;
}
//#endregion
//#region src/plugins/OpenLyric/preview/controller/config-text-editing.ts
/**
* In-preview editing of the free-text `Config` fields — Title, Subtitle,
* Description, Artist, Copyright, Theme, Genre, Style, Keywords, Year and
* Melody.
*
* `Key`, `Time`, `Tempo`, `Locales`, `Structure`, `Attachments` and the
* strumming patterns all have a picker of their own already. These eleven have
* nothing to pick from: the reader types them. So the affordance is the value
* itself — click it, or the pencil beside it, which is what a keyboard reaches
* — and the rendered value is replaced in place by a text input holding the
* field's *source* value. Save writes that one line back through
* `replaceDocumentLineRange` and the panel re-renders from the new document
* text; the preview never keeps a DOM mutation of its own, so both panels,
* Monaco and the undo stack stay in step.
*
* Two things make the write safe against markup a re-render has left behind:
* only a line number travels on the control, and the line is re-read from the
* document and re-checked for this field's name before anything is replaced.
* The reader's text is also only ever written *after* the `- Field:` prefix the
* document already had, so an in-preview edit cannot invent a field, close the
* fence, or split one line into two.
*
* Markdown panel only. The lyric/presentation panel shares these delegated
* listeners, so every lookup here is scoped to `refs.preview`.
*/
/** `- Title:   Amazing Grace` → prefix, field name, separator, value. */
var CONFIG_FIELD_LINE_RE = /^(\s*-\s*([^:]+):)([ \t]*)(.*)$/;
/**
* What a reader types has to stay one line of a `Config` field.
*
* Newlines are the only characters that could turn one field into two — a
* pasted multi-line value is the realistic way in — so they collapse to
* spaces; the surrounding whitespace goes because the source line's own
* separator supplies it.
*/
function normalizeConfigTextValue(value) {
	return String(value ?? "").replace(/[\r\n\u2028\u2029]+/g, " ").trim();
}
/** The line as it should read once `nextValue` is in it, or `null`. */
function buildConfigTextFieldLine(sourceLine, fieldName, nextValue) {
	const fieldMatch = String(sourceLine ?? "").match(CONFIG_FIELD_LINE_RE);
	if (!fieldMatch) return null;
	if (normalizeConfigFieldName(fieldMatch[2].trim()) !== fieldName) return null;
	const normalizedValue = normalizeConfigTextValue(nextValue);
	const separatorText = normalizedValue ? fieldMatch[3] || " " : "";
	return `${fieldMatch[1]}${separatorText}${normalizedValue}`;
}
//#endregion
//#region src/plugins/OpenLyric/domain/parser/OLParser.ts
function isPromiseLike(value) {
	return Boolean(value) && typeof value.then === "function";
}
function normalizeText(value, label) {
	if (typeof value === "string") return value;
	if (value === null) return "";
	if (value instanceof String) return value.valueOf();
	throw new TypeError(`${label} must be a string.`);
}
function normalizeProcessor(processor, label) {
	if (typeof processor !== "function") throw new TypeError(`${label} must be a function.`);
	return processor;
}
function normalizeProcessorList(processors, label) {
	if (!processors) return [];
	if (Array.isArray(processors)) return processors.map((processor, index) => normalizeProcessor(processor, `${label}[${index}]`));
	return [normalizeProcessor(processors, label)];
}
function normalizeStageResult(result, label) {
	if (result === void 0) return;
	return normalizeText(result, label);
}
function normalizeParserResult(result) {
	return normalizeText(result, "markdown parser result");
}
function resolveProcessorOverride(overrideProcessors, defaultProcessors, label) {
	if (overrideProcessors === void 0) return defaultProcessors.slice();
	return normalizeProcessorList(overrideProcessors, label);
}
function resolveMarkdownParser(markdownParser) {
	if (!markdownParser) return null;
	if (typeof markdownParser === "function") return markdownParser;
	if (typeof markdownParser.parse === "function") return markdownParser.parse.bind(markdownParser);
	throw new TypeError("markdownParser must be a function or an object with a parse method.");
}
/**
* Runs markdown through a configurable pipeline:
* raw markdown -> pre-processors -> markdown parser -> post-processors -> HTML.
*/
var OLParser = class {
	constructor(options = {}) {
		const markdownParser = options.markdownParser ?? options.parser ?? options.marked ?? null;
		const preProcessors = options.preProcessors ?? options.beforeParse ?? options.beforeMarked ?? [];
		const postProcessors = options.postProcessors ?? options.afterParse ?? options.afterMarked ?? [];
		this.markdownParser = null;
		this.preProcessors = [];
		this.postProcessors = [];
		this.setPreProcessors(preProcessors);
		this.setPostProcessors(postProcessors);
		if (markdownParser) this.setMarkdownParser(markdownParser);
	}
	setMarkdownParser(markdownParser) {
		this.markdownParser = resolveMarkdownParser(markdownParser);
		return this;
	}
	clearMarkdownParser() {
		this.markdownParser = null;
		return this;
	}
	setPreProcessors(processors) {
		this.preProcessors = normalizeProcessorList(processors, "preProcessors");
		return this;
	}
	setBeforeMarkedProcessors(processors) {
		return this.setPreProcessors(processors);
	}
	setPostProcessors(processors) {
		this.postProcessors = normalizeProcessorList(processors, "postProcessors");
		return this;
	}
	setAfterMarkedProcessors(processors) {
		return this.setPostProcessors(processors);
	}
	addPreProcessor(processor) {
		this.preProcessors.push(normalizeProcessor(processor, "preProcessor"));
		return this;
	}
	addBeforeMarkedProcessor(processor) {
		return this.addPreProcessor(processor);
	}
	addPostProcessor(processor) {
		this.postProcessors.push(normalizeProcessor(processor, "postProcessor"));
		return this;
	}
	addAfterMarkedProcessor(processor) {
		return this.addPostProcessor(processor);
	}
	addBeforeParseProcessor(processor) {
		return this.addPreProcessor(processor);
	}
	addAfterParseProcessor(processor) {
		return this.addPostProcessor(processor);
	}
	clearPreProcessors() {
		this.preProcessors = [];
		return this;
	}
	clearBeforeMarkedProcessors() {
		return this.clearPreProcessors();
	}
	clearPostProcessors() {
		this.postProcessors = [];
		return this;
	}
	clearAfterMarkedProcessors() {
		return this.clearPostProcessors();
	}
	use(stage, processor) {
		const normalizedStage = String(stage || "").toLowerCase();
		if (normalizedStage === "pre" || normalizedStage === "beforeparse" || normalizedStage === "before-parse" || normalizedStage === "beforemarked" || normalizedStage === "before-marked") return this.addPreProcessor(processor);
		if (normalizedStage === "post" || normalizedStage === "afterparse" || normalizedStage === "after-parse" || normalizedStage === "aftermarked" || normalizedStage === "after-marked") return this.addPostProcessor(processor);
		throw new Error("Unknown stage. Use \"pre\", \"beforeParse\", \"beforeMarked\", \"post\", \"afterParse\", or \"afterMarked\".");
	}
	createContext(rawText = "", extraContext = {}) {
		const normalizedRawText = normalizeText(rawText, "raw markdown");
		const context = extraContext && typeof extraContext === "object" ? extraContext : {};
		context.parser = this;
		context.rawText = normalizedRawText;
		context.markdownText = normalizedRawText;
		context.parsedHtml = "";
		context.htmlText = "";
		context.stage = "idle";
		context.processorIndex = null;
		context.processorCount = 0;
		return context;
	}
	preprocess(rawText, context = {}) {
		const parseContext = this.createContext(rawText, context);
		const markdownText = this.runProcessorChain(parseContext.rawText, this.preProcessors, "preprocess", parseContext);
		parseContext.markdownText = markdownText;
		parseContext.stage = "complete";
		return markdownText;
	}
	beforeMarked(rawText, context = {}) {
		return this.preprocess(rawText, context);
	}
	postprocess(htmlText, context = {}) {
		const parseContext = context && typeof context === "object" ? context : {};
		const normalizedHtmlText = normalizeText(htmlText, "parsed html");
		parseContext.parser = this;
		parseContext.rawText = typeof parseContext.rawText === "string" ? parseContext.rawText : "";
		parseContext.markdownText = typeof parseContext.markdownText === "string" ? parseContext.markdownText : parseContext.rawText;
		parseContext.parsedHtml = normalizedHtmlText;
		parseContext.htmlText = normalizedHtmlText;
		parseContext.stage = "idle";
		parseContext.processorIndex = null;
		parseContext.processorCount = 0;
		const nextHtmlText = this.runProcessorChain(normalizedHtmlText, this.postProcessors, "postprocess", parseContext);
		parseContext.htmlText = nextHtmlText;
		parseContext.stage = "complete";
		return nextHtmlText;
	}
	afterMarked(htmlText, context = {}) {
		return this.postprocess(htmlText, context);
	}
	parse(rawText, options = {}) {
		return this.parseToResult(rawText, options).htmlText;
	}
	parseToResult(rawText, options = {}) {
		const parseContext = this.createContext(rawText, options.context);
		const markdownParser = this.getMarkdownParser(options.markdownParser ?? options.parser ?? options.marked);
		const preProcessors = resolveProcessorOverride(options.preProcessors ?? options.beforeParse ?? options.beforeMarked, this.preProcessors, "preProcessors");
		const postProcessors = resolveProcessorOverride(options.postProcessors ?? options.afterParse ?? options.afterMarked, this.postProcessors, "postProcessors");
		parseContext.markdownParser = markdownParser;
		parseContext.preProcessors = preProcessors.slice();
		parseContext.postProcessors = postProcessors.slice();
		const markdownText = this.runProcessorChain(parseContext.rawText, preProcessors, "preprocess", parseContext);
		parseContext.markdownText = markdownText;
		parseContext.stage = "parse";
		const parsedHtml = this.renderMarkdown(markdownText, markdownParser, parseContext);
		parseContext.parsedHtml = parsedHtml;
		const htmlText = this.runProcessorChain(parsedHtml, postProcessors, "postprocess", parseContext);
		parseContext.htmlText = htmlText;
		parseContext.stage = "complete";
		parseContext.processorIndex = null;
		parseContext.processorCount = 0;
		return {
			rawText: parseContext.rawText,
			markdownText,
			parsedHtml,
			htmlText,
			context: parseContext
		};
	}
	getMarkdownParser(overrideParser) {
		const markdownParser = overrideParser === void 0 ? this.markdownParser : resolveMarkdownParser(overrideParser);
		if (!markdownParser) throw new Error("No markdown parser configured. Pass one to the constructor, call setMarkdownParser(), or provide options.markdownParser.");
		return markdownParser;
	}
	renderMarkdown(markdownText, markdownParser = this.markdownParser, context = {}) {
		const result = this.getMarkdownParser(markdownParser)(markdownText, context);
		if (isPromiseLike(result)) throw new TypeError("markdownParser returned a Promise. OLParser only supports synchronous parsing right now.");
		return normalizeParserResult(result);
	}
	runProcessorChain(value, processors, stage, context) {
		let nextValue = value;
		context.stage = stage;
		context.processorCount = processors.length;
		for (let index = 0; index < processors.length; index += 1) {
			const processor = processors[index];
			context.processorIndex = index;
			const result = processor(nextValue, context);
			if (isPromiseLike(result)) throw new TypeError(`${stage} processor at index ${index} returned a Promise. OLParser only supports synchronous processors right now.`);
			const normalizedResult = normalizeStageResult(result, `${stage} processor at index ${index}`);
			if (normalizedResult !== void 0) nextValue = normalizedResult;
		}
		context.processorIndex = null;
		return nextValue;
	}
};
//#endregion
//#region src/plugins/OpenLyric/preview/helpers.ts
var DIRECTIVE_TOKEN_RE = /(\{[^{}\r\n]+\})/g;
var CHORD_TOKEN_RE = /(\[[^\[\]\r\n]+\])/g;
var BAR_TOKEN_RE = /(\|\|:|\|:|:\|\||:\||\|)/g;
var REPEAT_TOKEN_RE = /\(([1-9]\d*x)\)/g;
var PLAIN_OL_TOKEN_RE$1 = /(\{[^{}\r\n]+\}|\|\|:|\|:|:\|\||:\||\||\([1-9]\d*x\))/g;
var INLINE_OL_TOKEN_RE = /(\[[^\[\]\r\n]+\]|\{[^{}\r\n]+\}|\|\|:|\|:|:\|\||:\||\||\([1-9]\d*x\))/g;
var HAS_CHORD_TOKEN_RE = /\[[^\[\]\r\n]+\]/;
var BARE_CHORD_RE$2 = new RegExp(`^${CHORD_SYMBOL_SOURCE}$`);
var CHORD_PLACEHOLDER_ATTRIBUTE = "data-ol-chord-placeholder";
var FONT_COLOR_TAG_RE = /<\/font\s*>|<font\b[^>]*>/gi;
var FONT_COLOR_ATTRIBUTE_RE = /\bcolor\s*=\s*(?:"([^"]*)"|'([^']*)'|([^\s"'=<>`]+))/i;
var MARKDOWN_PROTOCOL_LINK_RE = /(!?\[[^\]\r\n]*\]\()([A-Za-z][A-Za-z0-9+.-]*:\/\/[^)\r\n]+)(\))/g;
var STANDALONE_PROTOCOL_URL_RE = /^(\s*)([A-Za-z][A-Za-z0-9+.-]*:\/\/\S[^\r\n]*)(\s*)$/;
var STRUMMING_DOWN_SYMBOLS = /* @__PURE__ */ new Set([
	"d",
	"D",
	"v",
	"V"
]);
var STRUMMING_UP_SYMBOLS = /* @__PURE__ */ new Set([
	"u",
	"U",
	"^"
]);
var STRUMMING_DEFAULT_SYMBOLS = /* @__PURE__ */ new Set([
	"x",
	"X",
	"1",
	"*",
	"+"
]);
var STRUMMING_REST_SYMBOLS = /* @__PURE__ */ new Set([
	"-",
	"_",
	".",
	"0"
]);
var PREVIEW_TAB_WIDTH = 4;
var STRUMMING_PATTERN_DIRECTIVE_RE = /^\{p:(\s*)#([1-9]\d*)(\s*)\}$/;
var previewColorProbeElement = null;
var STRUMMING_TIME_SIGNATURES = /* @__PURE__ */ new Map([
	["4/4", {
		labelMode: "quarter",
		beatGroups: [
			4,
			4,
			4,
			4
		]
	}],
	["2/2", {
		labelMode: "quarter",
		beatGroups: [8, 8]
	}],
	["2/4", {
		labelMode: "quarter",
		beatGroups: [4, 4]
	}],
	["3/4", {
		labelMode: "quarter",
		beatGroups: [
			4,
			4,
			4
		]
	}],
	["3/8", {
		labelMode: "eighth",
		beatGroups: [
			2,
			2,
			2
		]
	}],
	["6/8", {
		labelMode: "eighth",
		beatGroups: [6, 6]
	}],
	["9/8", {
		labelMode: "eighth",
		beatGroups: [
			6,
			6,
			6
		]
	}],
	["12/8", {
		labelMode: "eighth",
		beatGroups: [
			6,
			6,
			6,
			6
		]
	}]
]);
function escapeHtml$1(input) {
	return String(input ?? "").replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/\"/g, "&quot;").replace(/'/g, "&#039;");
}
function normalizeExternalLinkAttributes(element) {
	if (!(element instanceof HTMLAnchorElement)) return;
	const href = element.getAttribute("href")?.trim() || "";
	if (!href || href.startsWith("#")) return;
	element.setAttribute("target", "_blank");
	const relValues = new Set((element.getAttribute("rel") || "").split(/\s+/).map((value) => value.trim()).filter(Boolean));
	relValues.add("noopener");
	relValues.add("noreferrer");
	element.setAttribute("rel", Array.from(relValues).join(" "));
}
function sanitizeHtml(html) {
	const doc = new DOMParser().parseFromString(html, "text/html");
	doc.querySelectorAll("script, style, iframe, object, embed, link, meta").forEach((node) => {
		node.remove();
	});
	doc.querySelectorAll("*").forEach((element) => {
		Array.from(element.attributes).forEach((attribute) => {
			const name = attribute.name.toLowerCase();
			const value = attribute.value.toLowerCase().trim();
			if (name.startsWith("on")) {
				element.removeAttribute(attribute.name);
				return;
			}
			if ((name === "href" || name === "src") && value.startsWith("javascript:")) element.removeAttribute(attribute.name);
		});
		normalizeExternalLinkAttributes(element);
	});
	return doc.body.innerHTML;
}
function normalizeNewlines$2(value) {
	return String(value).replace(/\r\n?/g, "\n");
}
function encodeSpacesInProtocolUrl(value) {
	return String(value ?? "").replace(/ /g, "%20");
}
function normalizeMarkdownRenderableUrls(value) {
	const source = String(value ?? "");
	if (!source.includes(" ")) return source;
	const normalizedLinks = source.replace(MARKDOWN_PROTOCOL_LINK_RE, (_match, prefix, url, suffix) => {
		return `${prefix}${encodeSpacesInProtocolUrl(url)}${suffix}`;
	});
	const standaloneUrlMatch = normalizedLinks.match(STANDALONE_PROTOCOL_URL_RE);
	if (!standaloneUrlMatch) return normalizedLinks;
	return `${standaloneUrlMatch[1]}${encodeSpacesInProtocolUrl(standaloneUrlMatch[2])}${standaloneUrlMatch[3]}`;
}
function getLineNumberAtOffset$1(text, offset) {
	if (offset <= 0) return 1;
	return text.slice(0, offset).split("\n").length;
}
function getEditorDataAttributes$1(lineNumber, column = 1) {
	if (!lineNumber) return "";
	return ` data-editor-line="${escapeHtml$1(lineNumber)}" data-editor-column="${escapeHtml$1(column || 1)}"`;
}
function getFenceHeaderEditorDataAttributes(startLineNumber) {
	if (!startLineNumber) return "";
	return getEditorDataAttributes$1(startLineNumber, 7);
}
function resolveAllowZwspSeparators(value, allowZwspSeparators) {
	return typeof allowZwspSeparators === "boolean" ? allowZwspSeparators : shouldAllowInvisibleWordSeparators(value);
}
function isCommentLine(line, allowZwspSeparators = true) {
	return trimSpaceLikeStart(line, allowZwspSeparators).startsWith("//");
}
function getFirstContentColumn$1(line, allowZwspSeparators = true) {
	const source = String(line ?? "");
	let firstContentIndex = 0;
	while (firstContentIndex < source.length && isSpaceLikeCharacter(source[firstContentIndex], allowZwspSeparators)) firstContentIndex += 1;
	return firstContentIndex >= source.length ? 1 : firstContentIndex + 1;
}
/**
* Split a fence body into the entries every preview renders from.
*
* Comment lines (`// …`) are authoring notes, so they are dropped by default —
* that is what both previews have always shown. `includeComments` keeps them
* instead, flagged `isComment` so the renderer can style them and every
* consumer that counts or exports lines can filter them back out.
*/
function createPreviewLineEntries(body, sourceLocation = null, allowZwspSeparators = shouldAllowInvisibleWordSeparators(body), includeComments = false) {
	const normalizedBody = String(body ?? "").replace(/\r\n?/g, "\n");
	const trimmedBody = normalizedBody.endsWith("\n") ? normalizedBody.slice(0, -1) : normalizedBody;
	if (!trimmedBody.length) return [];
	const startLineNumber = sourceLocation?.startLineNumber || 0;
	return trimmedBody.split("\n").flatMap((line, index) => {
		const isComment = isCommentLine(line, allowZwspSeparators);
		if (isComment && !includeComments) return [];
		return [{
			text: line,
			lineNumber: startLineNumber ? startLineNumber + 1 + index : null,
			column: getFirstContentColumn$1(line, allowZwspSeparators),
			...isComment ? { isComment: true } : {}
		}];
	});
}
function getPreviewSourceLocation(body, startLineNumber) {
	const bodyLines = normalizeNewlines$2(body).split("\n");
	const allowZwspSeparators = shouldAllowInvisibleWordSeparators(body);
	for (let index = 0; index < bodyLines.length; index += 1) {
		const line = bodyLines[index];
		if (!trimSpaceLikeText(line, allowZwspSeparators) || isCommentLine(line, allowZwspSeparators)) continue;
		return {
			startLineNumber,
			bodyLineNumber: startLineNumber + 1 + index,
			bodyColumn: getFirstContentColumn$1(line, allowZwspSeparators)
		};
	}
	return {
		startLineNumber,
		bodyLineNumber: startLineNumber + 1,
		bodyColumn: 1
	};
}
function renderStructureDeclarePartAction(insertIndex = 0) {
	return [
		"<div class=\"ol-preview-config__structure-action\">",
		`<button class="ol-preview-config__part-action" type="button" data-preview-action="toggle-declare-part-menu" data-structure-insert-index="${escapeHtml$1(insertIndex)}" aria-haspopup="menu" aria-expanded="false" aria-label="Add part to Structure" title="Add part to Structure">+</button>`,
		"</div>"
	].join("");
}
function renderStructureInsertAction(insertIndex, previousStep, nextStep) {
	const actionLabel = `Insert part between ${previousStep.partName || previousStep.partText || "part"} and ${nextStep.partName || nextStep.partText || "part"}`;
	return `<button class="ol-preview-structure-arrow ol-preview-structure-arrow-button" type="button" data-preview-action="toggle-declare-part-menu" data-structure-insert-index="${escapeHtml$1(insertIndex)}" aria-haspopup="menu" aria-expanded="false" aria-label="${escapeHtml$1(actionLabel)}" title="${escapeHtml$1(actionLabel)}">&rarr;</button>`;
}
function renderStructureRepeatControls(step, stepIndex) {
	const repeatCount = step.repeatText ? Number.parseInt(step.repeatText, 10) : 1;
	const partName = step.partName || step.partText || "part";
	const decreaseLabel = repeatCount > 1 ? `Decrease repeat for ${partName}` : `Remove ${partName} from Structure`;
	return [
		"<span class=\"ol-preview-structure-repeat-controls\">",
		`<button class="ol-preview-structure-repeat-button" type="button" data-preview-action="decrease-structure-repeat" data-structure-step-index="${escapeHtml$1(stepIndex)}" aria-label="${escapeHtml$1(decreaseLabel)}" title="${escapeHtml$1(decreaseLabel)}">-</button>`,
		`<button class="ol-preview-structure-repeat-button" type="button" data-preview-action="increase-structure-repeat" data-structure-step-index="${escapeHtml$1(stepIndex)}" aria-label="Increase repeat for ${escapeHtml$1(partName)}" title="Increase repeat for ${escapeHtml$1(partName)}">+</button>`,
		"</span>"
	].join("");
}
function renderStructureValue(values) {
	if (!Array.isArray(values) || values.length !== 1) return (values || []).map((value) => `<span${getEditorDataAttributes$1(value.lineEntry?.lineNumber, value.valueColumn || value.lineEntry?.column)}>${renderInlineOlText(value.text)}</span>`).join("<br>");
	const [value] = values;
	const parsedStructure = parseStructureValue(value.text);
	if (parsedStructure.error) return `<span${getEditorDataAttributes$1(value.lineEntry?.lineNumber, value.valueColumn || value.lineEntry?.column)}>${renderInlineOlText(value.text)}</span>`;
	if (!parsedStructure.steps.length) return `<div class="ol-preview-config__structure-value ol-preview-config__structure-value--empty"${getEditorDataAttributes$1(value.lineEntry?.lineNumber, value.valueColumn || value.lineEntry?.column)}>${renderStructureDeclarePartAction(0)}</div>`;
	const declarePartActionHtml = renderStructureDeclarePartAction(parsedStructure.steps.length);
	return `<div class="ol-preview-config__structure-value"><div class="ol-preview-structure-line">${parsedStructure.steps.map((step, index) => {
		const targetId = step.parsedHeader ? createPreviewTargetId(step.partName) : "";
		const editorLine = value.lineEntry?.lineNumber;
		const editorColumn = (value.valueColumn || value.lineEntry?.column || 1) + step.startOffset;
		const label = formatStructureStepLabel(step);
		return `<span class="ol-preview-structure-link">${`<span class="ol-preview-structure-step-shell">${targetId ? `<a class="ol-preview-structure-step" href="#${escapeHtml$1(targetId)}" data-preview-target-id="${escapeHtml$1(targetId)}"${getEditorDataAttributes$1(editorLine, editorColumn)}${step.header ? ` data-ol-header="${escapeHtml$1(step.header)}"` : ""}>${renderInlineOlText(label)}</a>` : `<span class="ol-preview-structure-step"${getEditorDataAttributes$1(editorLine, editorColumn)}${step.header ? ` data-ol-header="${escapeHtml$1(step.header)}"` : ""}>${renderInlineOlText(label)}</span>`}${renderStructureRepeatControls(step, index)}</span>`}${index < parsedStructure.steps.length - 1 ? renderStructureInsertAction(index + 1, step, parsedStructure.steps[index + 1]) : ""}</span>`;
	}).join("")}</div>${declarePartActionHtml}</div>`;
}
function renderOlSpecialToken(token, viewOptions = {}) {
	if (token.startsWith("{")) return renderPatternDirectiveToken(token, viewOptions) || `<span class="ol-preview-directive">${escapeHtml$1(token)}</span>`;
	if (token.startsWith("(")) return `<span class="ol-preview-repeat">${escapeHtml$1(token.replace(/^\((.*)\)$/, "$1"))}</span>`;
	return renderPreviewBarToken(token);
}
function renderPreviewBarToken(token, options = {}) {
	const classNames = ["ol-preview-bar"];
	if (options.hidden) classNames.push("ol-preview-bar--hidden");
	return `<span class="${classNames.join(" ")}"${options.hidden ? " aria-hidden=\"true\"" : ""}>${escapeHtml$1(token)}</span>`;
}
function normalizePreviewViewOptions(viewOptions) {
	const normalizedViewOptions = viewOptions && typeof viewOptions === "object" ? viewOptions : {};
	const hideBracketedKeys = Boolean(normalizedViewOptions.hideBracketedKeys);
	return {
		hideBracketedKeys,
		hideLeadingBars: Boolean(normalizedViewOptions.hideLeadingBars || hideBracketedKeys),
		showComments: Boolean(normalizedViewOptions.showComments),
		labels: normalizedViewOptions.labels && typeof normalizedViewOptions.labels === "object" ? normalizedViewOptions.labels : null,
		patternPreviewContext: normalizedViewOptions.patternPreviewContext || null,
		patternPreviewTargetIdPrefix: String(normalizedViewOptions.patternPreviewTargetIdPrefix ?? "").trim()
	};
}
/**
* The text a preview prints for one of its fixed labels — an `ol:Config` field
* name, `Untitled Song`. `labels` is the render option a language plugin's
* `language.labels` arrives as, keyed by the English label; a label it does
* not translate stays as it is.
*/
function translatePreviewLabel(labels, label) {
	const key = String(label ?? "");
	const translation = labels && typeof labels === "object" && Object.prototype.hasOwnProperty.call(labels, key) ? labels[key] : "";
	return typeof translation === "string" && translation.trim() ? translation.trim() : key;
}
function parseConfigPreviewValueMap(configBody, allowZwspSeparators = true) {
	const configValueMap = /* @__PURE__ */ new Map();
	let activeFieldName = "";
	for (const line of normalizeNewlines$2(configBody).split("\n")) {
		if (!trimSpaceLikeText(line, allowZwspSeparators)) continue;
		const fieldMatch = line.match(/^\s*-\s*([^:]+):\s*(.*)$/);
		if (fieldMatch) {
			activeFieldName = normalizeConfigFieldName(fieldMatch[1]);
			configValueMap.set(activeFieldName, [trimSpaceLikeText(fieldMatch[2], allowZwspSeparators)]);
			continue;
		}
		if (!activeFieldName || !/^[ \t]+/.test(line)) {
			activeFieldName = "";
			continue;
		}
		const activeValues = configValueMap.get(activeFieldName);
		if (!Array.isArray(activeValues)) {
			activeFieldName = "";
			continue;
		}
		activeValues.push(trimSpaceLikeText(line, allowZwspSeparators));
	}
	return configValueMap;
}
function getConfigPreviewValueLines(configValueMap, fieldName) {
	const values = configValueMap.get(normalizeConfigFieldName(fieldName));
	if (!Array.isArray(values)) return [];
	return values.map((value) => trimSpaceLikeText(value)).filter(Boolean);
}
function getConfigPreviewValue(configValueMap, fieldName) {
	return getConfigPreviewValueLines(configValueMap, fieldName).join(" ");
}
function getConfigPreviewFieldLineEntries(configBody, fieldName, options = {}) {
	const normalizedFieldName = normalizeConfigFieldName(fieldName);
	const allowZwspSeparators = resolveAllowZwspSeparators(configBody, options.allowZwspSeparators);
	if (!normalizedFieldName) return [];
	const normalizedBody = normalizeNewlines$2(configBody);
	const trimmedBody = normalizedBody.endsWith("\n") ? normalizedBody.slice(0, -1) : normalizedBody;
	if (!trimmedBody.length) return [];
	const preserveComments = Boolean(options.preserveComments);
	const startLineNumber = options.sourceLocation?.startLineNumber || 0;
	const valueEntries = [];
	let activeFieldName = "";
	trimmedBody.split("\n").forEach((line, index) => {
		if (!trimSpaceLikeText(line, allowZwspSeparators)) return;
		const fieldMatch = line.match(/^\s*-\s*([^:]+):\s*(.*)$/);
		if (fieldMatch) {
			activeFieldName = normalizeConfigFieldName(fieldMatch[1]);
			if (activeFieldName !== normalizedFieldName) return;
			const separatorOffset = line.indexOf(":");
			const valueOffset = separatorOffset === -1 ? line.length : separatorOffset + 1;
			const valueIndentLength = getLeadingSpaceLikeLength(line.slice(valueOffset), allowZwspSeparators);
			const lineNumber = startLineNumber ? startLineNumber + 1 + index : null;
			valueEntries.push({
				text: fieldMatch[2],
				lineEntry: {
					text: line,
					lineNumber,
					column: getFirstContentColumn$1(line, allowZwspSeparators)
				},
				valueColumn: valueOffset + valueIndentLength + 1,
				sourceIndex: valueEntries.length
			});
			return;
		}
		if (!activeFieldName || !/^[ \t]+/.test(line)) {
			activeFieldName = "";
			return;
		}
		if (activeFieldName !== normalizedFieldName) return;
		if (isCommentLine(line, allowZwspSeparators) && !preserveComments) return;
		const lineNumber = startLineNumber ? startLineNumber + 1 + index : null;
		valueEntries.push({
			text: trimSpaceLikeText(line, allowZwspSeparators),
			lineEntry: {
				text: line,
				lineNumber,
				column: getFirstContentColumn$1(line, allowZwspSeparators)
			},
			valueColumn: getFirstContentColumn$1(line, allowZwspSeparators),
			sourceIndex: valueEntries.length
		});
	});
	return valueEntries;
}
function createStrummingPatternPreviewContextFromConfigBody(configBody, options = {}) {
	const allowZwspSeparators = resolveAllowZwspSeparators(configBody, options.allowZwspSeparators);
	if (!trimSpaceLikeText(configBody, allowZwspSeparators)) return null;
	const configValueMap = parseConfigPreviewValueMap(configBody, allowZwspSeparators);
	const patterns = parseStrummingPatterns(getConfigPreviewFieldLineEntries(configBody, "Strumming Patterns", {
		allowZwspSeparators,
		preserveComments: true,
		sourceLocation: options.sourceLocation
	}), { allowZwspSeparators }).map((pattern, zeroBasedIndex) => ({
		...pattern,
		allowZwspSeparators,
		referenceIndex: zeroBasedIndex + 1
	}));
	if (!patterns.length) return null;
	return {
		allowZwspSeparators,
		keyText: trimSpaceLikeText(options.keyTextOverride, allowZwspSeparators) || getConfigPreviewValue(configValueMap, "Key"),
		patterns,
		patternsByIndex: new Map(patterns.map((pattern) => [pattern.referenceIndex, pattern])),
		tempoText: getConfigPreviewValue(configValueMap, "Tempo"),
		timeSignatureText: getConfigPreviewValue(configValueMap, "Time") || "4/4"
	};
}
function createStrummingPatternPreviewContextFromMarkdown(markdown, options = {}) {
	const normalizedMarkdown = normalizeNewlines$2(markdown);
	OL_FENCE_BLOCK_RE$1.lastIndex = 0;
	for (const match of normalizedMarkdown.matchAll(OL_FENCE_BLOCK_RE$1)) {
		if (parseFenceHeader(String(match[1] || "").trim())?.kind !== "config") continue;
		const matchOffset = match.index || 0;
		return createStrummingPatternPreviewContextFromConfigBody(match[2] || "", {
			...options,
			sourceLocation: { startLineNumber: getLineNumberAtOffset$1(normalizedMarkdown, matchOffset) }
		});
	}
	return null;
}
function renderPatternDirectiveToken(token, viewOptions = {}) {
	const directiveMatch = String(token ?? "").match(STRUMMING_PATTERN_DIRECTIVE_RE);
	if (!directiveMatch) return "";
	const [, leadingWhitespace, patternIndexText, trailingWhitespace] = directiveMatch;
	const normalizedViewOptions = normalizePreviewViewOptions(viewOptions);
	const patternPreviewContext = normalizedViewOptions.patternPreviewContext;
	const patternIndex = Number.parseInt(patternIndexText, 10);
	const pattern = patternPreviewContext?.patternsByIndex?.get(patternIndex);
	if (!pattern) return "";
	const patternLabel = String(pattern.label ?? "").trim() || `Pattern ${patternIndex}`;
	const targetId = createPatternPreviewTargetId(normalizedViewOptions.patternPreviewTargetIdPrefix, patternIndex);
	const targetAttribute = targetId ? ` data-preview-target-id="${escapeHtml$1(targetId)}"` : "";
	const interactionLabel = targetId ? `Jump to ${patternLabel} preview` : `Preview ${patternLabel}`;
	return [
		"<span class=\"ol-preview-directive\">",
		"{p:",
		escapeHtml$1(leadingWhitespace),
		`<button class="ol-preview-pattern-reference" type="button" data-pattern-reference-index="${escapeHtml$1(patternIndexText)}" data-pattern-reference-label="${escapeHtml$1(patternLabel)}" data-pattern-reference-source="${escapeHtml$1(pattern.pattern)}"${targetAttribute}${getStrummingPatternPreviewDataAttributes({
			keyText: patternPreviewContext.keyText,
			tempoText: patternPreviewContext.tempoText,
			timeSignatureText: patternPreviewContext.timeSignatureText
		})} aria-label="${escapeHtml$1(interactionLabel)}" title="${escapeHtml$1(interactionLabel)}">#${escapeHtml$1(patternIndexText)}</button>`,
		escapeHtml$1(trailingWhitespace),
		"}",
		"</span>"
	].join("");
}
function createPatternPreviewTargetId(prefix, patternIndex) {
	const normalizedPrefix = String(prefix ?? "").trim();
	if (!normalizedPrefix || !Number.isInteger(patternIndex) || patternIndex < 1) return "";
	return `${normalizedPrefix}-${patternIndex}`;
}
function createFontColorState() {
	return { stack: [] };
}
function getPreviewColorProbeElement() {
	if (typeof document === "undefined") return null;
	if (!previewColorProbeElement) previewColorProbeElement = document.createElement("span");
	return previewColorProbeElement;
}
function normalizePreviewTextColor(value) {
	const trimmedValue = String(value ?? "").trim();
	if (!trimmedValue) return "";
	const probeElement = getPreviewColorProbeElement();
	if (!probeElement) return trimmedValue;
	probeElement.style.color = "";
	probeElement.style.color = trimmedValue;
	return probeElement.style.color ? trimmedValue : "";
}
function getFontColorTagValue(tagText) {
	const colorMatch = String(tagText ?? "").match(FONT_COLOR_ATTRIBUTE_RE);
	return normalizePreviewTextColor(colorMatch?.[1] || colorMatch?.[2] || colorMatch?.[3] || "");
}
function getInlineTextSegmentsWithFontColors(value, state) {
	const source = String(value ?? "");
	const fontColorState = state || createFontColorState();
	const segments = [];
	let currentText = "";
	let lastIndex = 0;
	const pushCurrentText = () => {
		if (!currentText) return;
		segments.push({
			color: fontColorState.stack[fontColorState.stack.length - 1]?.color || "",
			text: currentText
		});
		currentText = "";
	};
	FONT_COLOR_TAG_RE.lastIndex = 0;
	for (const match of source.matchAll(FONT_COLOR_TAG_RE)) {
		const matchIndex = match.index ?? 0;
		const tagText = match[0] || "";
		currentText += source.slice(lastIndex, matchIndex);
		if (/^<font\b/i.test(tagText)) {
			const color = getFontColorTagValue(tagText);
			if (color) {
				pushCurrentText();
				fontColorState.stack.push({ color });
			} else currentText += tagText;
		} else if (/^<\/font/i.test(tagText) && fontColorState.stack.length) {
			pushCurrentText();
			fontColorState.stack.pop();
		} else currentText += tagText;
		lastIndex = matchIndex + tagText.length;
	}
	currentText += source.slice(lastIndex);
	pushCurrentText();
	return segments;
}
function buildLineSourceFromTextSegments(segments) {
	return (segments || []).map((segment) => {
		if (!segment?.text) return "";
		if (!segment.color) return segment.text;
		return `<span style="color: ${escapeHtml$1(segment.color)}">${segment.text}</span>`;
	}).join("");
}
function renderTextSegments(segments, renderText) {
	return (segments || []).map((segment) => {
		if (!segment?.text) return "";
		const renderedSegment = renderText(segment.text);
		if (!segment.color) return renderedSegment;
		return `<span style="color: ${escapeHtml$1(segment.color)}">${renderedSegment}</span>`;
	}).join("");
}
function preserveTextNodeWhitespace(value) {
	return String(value ?? "").replace(/\t/g, "\xA0".repeat(PREVIEW_TAB_WIDTH)).replace(/(^|[\r\n])( +)/g, (_match, prefix, spaces) => {
		return `${prefix}${"\xA0".repeat(spaces.length)}`;
	}).replace(/ {2,}/g, (match) => "\xA0".repeat(match.length)).replace(/( +)(?=$|[\r\n])/g, (match) => "\xA0".repeat(match.length));
}
function preserveRenderedWhitespace(html) {
	const source = String(html ?? "");
	if (!source || typeof document === "undefined") return source;
	const container = document.createElement("div");
	container.innerHTML = source;
	const textNodes = [];
	const collectTextNodes = (node) => {
		node.childNodes.forEach((childNode) => {
			if (childNode.nodeType === Node.TEXT_NODE) {
				textNodes.push(childNode);
				return;
			}
			if (childNode.nodeType === Node.ELEMENT_NODE) collectTextNodes(childNode);
		});
	};
	collectTextNodes(container);
	textNodes.forEach((textNode) => {
		const preservedText = preserveTextNodeWhitespace(textNode.nodeValue || "");
		if (preservedText !== textNode.nodeValue) textNode.nodeValue = preservedText;
	});
	return container.innerHTML;
}
function renderInlineMarkdownText(value) {
	const source = normalizeMarkdownRenderableUrls(value);
	if (!source) return "";
	if (!source.trim()) return escapeHtml$1(source);
	return sanitizeHtml(marked.parseInline(source, {
		gfm: true,
		breaks: true
	}));
}
function renderHtmlFragmentPlainText(html) {
	const source = String(html ?? "");
	if (!source) return "";
	if (typeof DOMParser === "undefined") return source.replace(/<br\s*\/?>/gi, "\n").replace(/<[^>]+>/g, "");
	return new DOMParser().parseFromString(source.replace(/<br\s*\/?>/gi, "\n"), "text/html").body.textContent || "";
}
function renderInlineTextPlainText(value) {
	return getInlineTextSegmentsWithFontColors(value).map((segment) => {
		return renderHtmlFragmentPlainText(renderInlineMarkdownText(segment.text));
	}).join("").replace(/\u00A0/g, " ");
}
function renderPlainOlText(value, viewOptions = {}) {
	const source = String(value ?? "");
	let html = "";
	let lastIndex = 0;
	for (const match of source.matchAll(PLAIN_OL_TOKEN_RE$1)) {
		const matchIndex = match.index ?? 0;
		const token = match[0];
		html += renderInlineMarkdownText(source.slice(lastIndex, matchIndex));
		html += renderOlSpecialToken(token, viewOptions);
		lastIndex = matchIndex + token.length;
	}
	html += renderInlineMarkdownText(source.slice(lastIndex));
	return html;
}
function getChordKey(chordToken) {
	return String(chordToken ?? "").trim().replace(/^\[/, "").replace(/\]$/, "");
}
function renderChordToken(chordToken, options = {}) {
	const chordKey = getChordKey(chordToken);
	const escapedChordKey = escapeHtml$1(chordKey);
	const chordTitle = escapeHtml$1(describeChordKey(chordKey));
	const preserveBracketSpacing = Boolean(options.preserveBracketSpacing);
	const hidden = Boolean(options.hidden);
	const classNames = ["ol-preview-chord"];
	if (preserveBracketSpacing) classNames.push("ol-preview-chord--with-brackets");
	if (hidden) classNames.push("ol-preview-chord--hidden");
	if (preserveBracketSpacing) return `<button class="${classNames.join(" ")}" type="button" data-chord-key="${escapedChordKey}" data-chord-title="${chordTitle}" aria-label="Show ${chordTitle}"${hidden ? " aria-hidden=\"true\"" : ""}><span class="ol-preview-chord__bracket" aria-hidden="true">[</span><span class="ol-preview-chord__label">${escapedChordKey}</span><span class="ol-preview-chord__bracket" aria-hidden="true">]</span></button>`;
	return `<button class="${classNames.join(" ")}" type="button" data-chord-key="${escapedChordKey}" data-chord-title="${chordTitle}" aria-label="Show ${chordTitle}"${hidden ? " aria-hidden=\"true\"" : ""}>${escapedChordKey}</button>`;
}
function renderChordedLyricChordToken(chordToken, viewOptions = {}) {
	const normalizedChordToken = String(chordToken ?? "");
	const { hideLeadingBars } = normalizePreviewViewOptions(viewOptions);
	if (!normalizedChordToken) return "";
	if (normalizedChordToken.startsWith("|")) {
		if (hideLeadingBars) return `${renderPreviewBarToken("|", { hidden: true })}${renderInlineOlText(normalizedChordToken.slice(1), viewOptions)}`;
		return renderInlineOlText(normalizedChordToken, viewOptions);
	}
	return `${renderPreviewBarToken("|", { hidden: true })}${renderInlineOlText(normalizedChordToken, viewOptions)}`;
}
function shouldHideInlineBarToken(matches, matchIndex, source) {
	const currentMatch = matches[matchIndex];
	const nextMatch = matches[matchIndex + 1];
	if (!currentMatch || currentMatch[0] !== "|" || !nextMatch) return false;
	const nextToken = nextMatch[0] || "";
	const isChordToken = CHORD_TOKEN_RE.test(nextToken);
	CHORD_TOKEN_RE.lastIndex = 0;
	if (!isChordToken) return false;
	const nextIndex = nextMatch.index ?? 0;
	const currentIndex = currentMatch.index ?? 0;
	return !trimSpaceLikeText(source.slice(currentIndex + 1, nextIndex));
}
function renderInlineOlText(value, viewOptions = {}) {
	const source = String(value ?? "");
	const { hideBracketedKeys } = normalizePreviewViewOptions(viewOptions);
	const matches = Array.from(source.matchAll(INLINE_OL_TOKEN_RE));
	let html = "";
	let lastIndex = 0;
	matches.forEach((match, index) => {
		const matchIndex = match.index ?? 0;
		const token = match[0];
		html += renderPlainOlText(source.slice(lastIndex, matchIndex), viewOptions);
		if (CHORD_TOKEN_RE.test(token)) {
			html += renderChordToken(token, {
				preserveBracketSpacing: true,
				hidden: hideBracketedKeys
			});
			CHORD_TOKEN_RE.lastIndex = 0;
		} else if (hideBracketedKeys && shouldHideInlineBarToken(matches, index, source)) html += renderPreviewBarToken(token, { hidden: true });
		else html += renderOlSpecialToken(token, viewOptions);
		lastIndex = matchIndex + token.length;
	});
	html += renderPlainOlText(source.slice(lastIndex), viewOptions);
	return html;
}
function renderChordProgressionSegment(value) {
	return String(value ?? "").split(/([\s\u200B]+)/u).map((segment) => {
		if (!segment) return "";
		if (!trimSpaceLikeText(segment)) return escapeHtml$1(segment);
		return BARE_CHORD_RE$2.test(segment) ? renderChordToken(segment) : escapeHtml$1(segment);
	}).join("");
}
function renderChordProgressionText(value, viewOptions = {}) {
	const source = String(value ?? "");
	let html = "";
	let lastIndex = 0;
	for (const match of source.matchAll(PLAIN_OL_TOKEN_RE$1)) {
		const matchIndex = match.index ?? 0;
		const token = match[0];
		html += renderChordProgressionSegment(source.slice(lastIndex, matchIndex));
		html += renderOlSpecialToken(token, viewOptions);
		lastIndex = matchIndex + token.length;
	}
	html += renderChordProgressionSegment(source.slice(lastIndex));
	return html;
}
function hasChordedLyricText(value) {
	const source = String(value ?? "");
	if (!HAS_CHORD_TOKEN_RE.test(source)) return false;
	return source.replace(CHORD_TOKEN_RE, "").replace(BAR_TOKEN_RE, "").replace(REPEAT_TOKEN_RE, "").replace(DIRECTIVE_TOKEN_RE, "").trim().length > 0;
}
function isChordOnlyLineText(value) {
	const source = String(value ?? "");
	if (!HAS_CHORD_TOKEN_RE.test(source) && !hasChordProgressionText(source)) return false;
	return !source.replace(CHORD_TOKEN_RE, " ").replace(BAR_TOKEN_RE, " ").replace(REPEAT_TOKEN_RE, " ").split(/[\s\u200B]+/u).some((segment) => segment && !BARE_CHORD_RE$2.test(segment));
}
/**
* Is this line pure chord notation — bars, chord symbols, repeat suffixes and
* `{p:}`/`{c:}` cues, with no lyric left over?
*
* `hasChordProgressionText` is the cheaper cousin but only says yes when a bar
* is present, and `isChordOnlyLineText` deliberately counts a cue directive as
* content. A mixed section (`Intro`, `Outro`) needs the strict reading to pick
* a rendering: a bar-less `C Am F G` and a bare `{c: Piano}` are both notation
* and must transpose, simplify and lay out as such, while `Still You are near`
* must not.
*/
function isProgressionLineText(value) {
	const source = String(value ?? "").trim();
	if (!source) return false;
	return source.replace(DIRECTIVE_TOKEN_RE, " ").replace(BAR_TOKEN_RE, " ").replace(REPEAT_TOKEN_RE, " ").split(/[\s​]+/u).filter(Boolean).every((segment) => BARE_CHORD_RE$2.test(segment));
}
function shouldFloatLeadingBar(value, chordStart, lastTextIndex) {
	const barIndex = chordStart - 1;
	if (barIndex < lastTextIndex || value[barIndex] !== "|") return false;
	const previousCharacter = value[barIndex - 1] || "";
	return previousCharacter !== "|" && previousCharacter !== ":";
}
function createChordPlaceholderHtml(index) {
	return `<span ${CHORD_PLACEHOLDER_ATTRIBUTE}="${escapeHtml$1(index)}"></span>`;
}
function renderHtmlFragment(fragment) {
	const container = document.createElement("div");
	container.append(fragment);
	return container.innerHTML;
}
function createChordedLyricSegments(value, viewOptions = {}) {
	const source = String(value ?? "");
	const chordTokens = [];
	let placeholderSource = "";
	let lastIndex = 0;
	for (const match of source.matchAll(CHORD_TOKEN_RE)) {
		const chordStart = match.index ?? 0;
		const chordEnd = chordStart + match[0].length;
		const labelStart = shouldFloatLeadingBar(source, chordStart, lastIndex) ? chordStart - 1 : chordStart;
		placeholderSource += source.slice(lastIndex, labelStart);
		placeholderSource += createChordPlaceholderHtml(chordTokens.length);
		chordTokens.push(source.slice(labelStart, chordEnd));
		lastIndex = chordEnd;
	}
	if (!chordTokens.length) return [];
	placeholderSource += source.slice(lastIndex);
	const renderedHtml = renderPlainOlText(placeholderSource, viewOptions);
	const container = document.createElement("div");
	container.innerHTML = renderedHtml;
	const placeholders = Array.from(container.querySelectorAll(`[${CHORD_PLACEHOLDER_ATTRIBUTE}]`));
	if (!placeholders.length) return [];
	const segments = [];
	const range = document.createRange();
	range.setStart(container, 0);
	range.setEndBefore(placeholders[0]);
	const leadingLyricHtml = renderHtmlFragment(range.cloneContents());
	if (leadingLyricHtml) segments.push({
		chord: "",
		lyricHtml: leadingLyricHtml
	});
	placeholders.forEach((placeholder, index) => {
		const placeholderIndex = Number(placeholder.getAttribute(CHORD_PLACEHOLDER_ATTRIBUTE));
		range.setStartAfter(placeholder);
		if (placeholders[index + 1]) range.setEndBefore(placeholders[index + 1]);
		else range.setEnd(container, container.childNodes.length);
		segments.push({
			chord: chordTokens[placeholderIndex] || "",
			lyricHtml: renderHtmlFragment(range.cloneContents())
		});
	});
	return segments;
}
function createChordedLyricTextLines(value, viewOptions = {}) {
	const source = String(value ?? "");
	const { hideBracketedKeys, hideLeadingBars } = normalizePreviewViewOptions(viewOptions);
	if (!hasChordedLyricText(source)) return [trimSpaceLikeEnd(source)];
	const chordPlacements = [];
	let lyricLine = "";
	let lastTextIndex = 0;
	for (const match of source.matchAll(CHORD_TOKEN_RE)) {
		const chordStart = match.index ?? 0;
		const chordEnd = chordStart + match[0].length;
		const floatedLeadingBar = shouldFloatLeadingBar(source, chordStart, lastTextIndex);
		const labelStart = floatedLeadingBar ? chordStart - 1 : chordStart;
		lyricLine += source.slice(lastTextIndex, labelStart);
		if (!hideBracketedKeys) chordPlacements.push({
			label: `${floatedLeadingBar && !hideLeadingBars ? "|" : ""}${getChordKey(match[0])}`,
			position: getTextColumnWidth(lyricLine)
		});
		lastTextIndex = chordEnd;
	}
	lyricLine += source.slice(lastTextIndex);
	const normalizedLyricLine = trimSpaceLikeEnd(lyricLine);
	if (hideBracketedKeys) return normalizedLyricLine ? [normalizedLyricLine] : [];
	let chordLine = "";
	chordPlacements.forEach(({ label, position }) => {
		const chordLineWidth = getTextColumnWidth(chordLine);
		if (position > chordLineWidth) chordLine += " ".repeat(position - chordLineWidth);
		chordLine += label;
	});
	return [trimSpaceLikeEnd(chordLine), normalizedLyricLine];
}
function renderChordedLyricText(value, viewOptions = {}) {
	const { hideBracketedKeys } = normalizePreviewViewOptions(viewOptions);
	const hiddenChordClassName = hideBracketedKeys ? " ol-preview-lyric-segment__chord--hidden" : "";
	return createChordedLyricSegments(value, viewOptions).map((segment) => {
		const chordHtml = segment.chord ? renderChordedLyricChordToken(segment.chord, viewOptions) : "&nbsp;";
		const lyricHtml = segment.lyricHtml?.length ? preserveRenderedWhitespace(segment.lyricHtml) : "&nbsp;";
		return [
			"<span class=\"ol-preview-lyric-segment\">",
			`<span class="ol-preview-lyric-segment__chord${segment.chord ? "" : " ol-preview-lyric-segment__chord--empty"}${hiddenChordClassName}">${chordHtml}</span>`,
			`<span class="ol-preview-lyric-segment__text">${lyricHtml}</span>`,
			"</span>"
		].join("");
	}).join("");
}
function renderEmptyFenceBody() {
	return "";
}
function renderLineCollection(lines, options = {}) {
	const viewOptions = normalizePreviewViewOptions(options.viewOptions);
	if (!lines.length) return renderEmptyFenceBody();
	const fontColorState = createFontColorState();
	const renderedLines = lines.map((line) => {
		const entry = typeof line === "string" ? {
			text: line,
			lineNumber: null,
			column: 1
		} : line;
		if (entry.isComment) return `<div class="ol-preview-line ol-preview-line--comment"${getEditorDataAttributes$1(entry.lineNumber, entry.column)}><span class="ol-preview-line__comment">${preserveRenderedWhitespace(escapeHtml$1(entry.text))}</span></div>`;
		const textSegments = getInlineTextSegmentsWithFontColors(entry.text, fontColorState);
		const visibleText = textSegments.map((segment) => segment.text).join("");
		if (viewOptions.hideBracketedKeys && isChordOnlyLineText(visibleText)) return "";
		const usesChordedLyricLayout = options.useChordedLyricLayout && hasChordedLyricText(visibleText);
		const usesProgressionLayout = Boolean(options.markProgressionLines) && !usesChordedLyricLayout && hasChordProgressionText(visibleText);
		const renderedLineText = typeof options.renderLineText === "function" ? preserveRenderedWhitespace(renderTextSegments(textSegments, options.renderLineText)) : preserveRenderedWhitespace(renderTextSegments(textSegments, (value) => renderInlineOlText(value, viewOptions)));
		const content = !entry.text.length ? "&nbsp;" : !visibleText.length ? "" : usesChordedLyricLayout ? `<span class="ol-preview-line__content ol-preview-line__content--chorded">${renderChordedLyricText(buildLineSourceFromTextSegments(textSegments), viewOptions)}</span>` : usesProgressionLayout ? `<span class="ol-preview-line__content ol-preview-line__content--progression">${renderedLineText}</span>` : renderedLineText;
		if (!content) return "";
		return `<div class="${usesChordedLyricLayout ? "ol-preview-line ol-preview-line--chorded" : usesProgressionLayout ? "ol-preview-line ol-preview-line--progression" : !entry.text.length ? "ol-preview-line ol-preview-line--blank" : "ol-preview-line"}"${getEditorDataAttributes$1(entry.lineNumber, entry.column)}>${content}</div>`;
	}).filter(Boolean);
	if (!renderedLines.length) return renderEmptyFenceBody();
	return [
		"<div class=\"ol-preview-lines\">",
		...renderedLines,
		"</div>"
	].join("");
}
function renderLyricLineCollection(lines, viewOptions = {}) {
	return renderLineCollection(lines, {
		useChordedLyricLayout: true,
		viewOptions
	});
}
function renderMixedLineCollection(lines, viewOptions = {}) {
	return renderLineCollection(lines, {
		useChordedLyricLayout: true,
		markProgressionLines: true,
		viewOptions,
		renderLineText(value) {
			return hasChordProgressionText(value) ? renderChordProgressionText(value, viewOptions) : renderInlineOlText(value, viewOptions);
		}
	});
}
function renderChordProgressionLineCollection(lines, viewOptions = {}) {
	return renderLineCollection(lines, {
		markProgressionLines: true,
		viewOptions,
		renderLineText(value) {
			return hasChordProgressionText(value) ? renderChordProgressionText(value, viewOptions) : renderInlineOlText(value, viewOptions);
		}
	});
}
function normalizeStrummingPatternLine(line) {
	if (line && typeof line === "object") return {
		allowZwspSeparators: Boolean(line.allowZwspSeparators),
		text: line.text,
		lineNumber: line.lineEntry?.lineNumber ?? line.lineNumber ?? null,
		column: line.valueColumn || line.lineEntry?.column || line.column || 1,
		rawLine: line.rawLine || "",
		sourceIndex: Number.isInteger(line.sourceIndex) ? line.sourceIndex : null
	};
	return {
		allowZwspSeparators: false,
		text: line,
		lineNumber: null,
		column: 1,
		rawLine: String(line ?? ""),
		sourceIndex: null
	};
}
function parseStrummingPatterns(lines, options = {}) {
	const patterns = [];
	let pendingLabel = "";
	let pendingLabelSourceIndex = null;
	const fallbackAllowZwspSeparators = resolveAllowZwspSeparators((lines || []).map((line) => {
		return typeof line === "object" ? line?.text : line;
	}).join("\n"), options.allowZwspSeparators);
	(lines || []).forEach((line, sourceIndex) => {
		const normalizedLine = normalizeStrummingPatternLine(line);
		const allowZwspSeparators = normalizedLine.allowZwspSeparators || fallbackAllowZwspSeparators;
		const trimmedLine = trimSpaceLikeText(normalizedLine.text, allowZwspSeparators);
		const resolvedSourceIndex = Number.isInteger(normalizedLine.sourceIndex) ? normalizedLine.sourceIndex : sourceIndex;
		if (!trimmedLine) return;
		if (isCommentLine(trimmedLine, allowZwspSeparators)) {
			pendingLabel = trimmedLine.replace(/^\/\/\s*/, "").trim();
			pendingLabelSourceIndex = resolvedSourceIndex;
			return;
		}
		patterns.push({
			label: pendingLabel || `Pattern #${patterns.length + 1}`,
			labelSourceIndex: pendingLabel ? pendingLabelSourceIndex : null,
			allowZwspSeparators,
			pattern: trimmedLine,
			lineNumber: normalizedLine.lineNumber,
			column: normalizedLine.column,
			sourceIndex: resolvedSourceIndex
		});
		pendingLabel = "";
		pendingLabelSourceIndex = null;
	});
	return patterns;
}
function getStrummingTimeSignatureDefinition(timeSignatureText) {
	return STRUMMING_TIME_SIGNATURES.get(String(timeSignatureText ?? "").trim()) || STRUMMING_TIME_SIGNATURES.get("4/4");
}
function getDefaultStrummingDirection(stepIndex) {
	return stepIndex % 2 === 0 ? "down" : "up";
}
function getStrummingStepLabel(stepIndex, timeSignature) {
	if (timeSignature.labelMode === "eighth") return {
		text: stepIndex % 2 === 0 ? String(Math.floor(stepIndex / 2) + 1) : "&",
		accent: stepIndex % 2 === 0
	};
	const phase = stepIndex % 4;
	if (phase === 0) return {
		text: String(Math.floor(stepIndex / 4) + 1),
		accent: true
	};
	return {
		text: [
			"",
			"e",
			"&",
			"a"
		][phase],
		accent: false
	};
}
function getStrummingBeatGuideGroups(stepCount, timeSignature) {
	if (!Number.isInteger(stepCount) || stepCount < 1) return [];
	const baseGroups = Array.isArray(timeSignature?.beatGroups) ? timeSignature.beatGroups.filter((groupSize) => Number.isInteger(groupSize) && groupSize > 0) : [];
	const resolvedBaseGroups = baseGroups.length ? baseGroups : [stepCount];
	const beatGuideGroups = [];
	let remainingSteps = stepCount;
	while (remainingSteps > 0) resolvedBaseGroups.forEach((groupSize, index) => {
		if (remainingSteps < 1) return;
		const span = Math.min(groupSize, remainingSteps);
		beatGuideGroups.push({
			label: String(index + 1),
			span
		});
		remainingSteps -= span;
	});
	return beatGuideGroups;
}
function renderStrummingBeatGuideRow(stepCount, timeSignature) {
	const beatGuideGroups = getStrummingBeatGuideGroups(stepCount, timeSignature);
	if (beatGuideGroups.length < 2) return "";
	return [
		"<div class=\"ol-song-view__pattern-row ol-song-view__pattern-row--guide\" aria-hidden=\"true\">",
		...beatGuideGroups.map((group, groupIndex) => {
			const classNames = ["ol-song-view__pattern-guide-cell"];
			if (groupIndex > 0) classNames.push("ol-song-view__pattern-guide-cell--break");
			return `<span class="${classNames.join(" ")}" style="grid-column: span ${group.span}">${escapeHtml$1(group.label)}</span>`;
		}),
		"</div>"
	].join("");
}
function parseStrummingPatternSteps(patternText, options = {}) {
	const steps = [];
	const breakBefore = /* @__PURE__ */ new Set();
	let stepIndex = 0;
	const allowZwspSeparators = resolveAllowZwspSeparators(patternText, options.allowZwspSeparators);
	const normalizedPatternText = normalizeStrummingPatternValue(patternText, allowZwspSeparators);
	for (let sourceOffset = 0; sourceOffset < normalizedPatternText.length; sourceOffset += 1) {
		const character = normalizedPatternText[sourceOffset];
		if (isSpaceLikeCharacter(character, allowZwspSeparators)) continue;
		if (character === "|") {
			if (stepIndex > 0) breakBefore.add(stepIndex);
			continue;
		}
		let direction = null;
		if (STRUMMING_DOWN_SYMBOLS.has(character)) direction = "down";
		else if (STRUMMING_UP_SYMBOLS.has(character)) direction = "up";
		else if (STRUMMING_DEFAULT_SYMBOLS.has(character)) direction = getDefaultStrummingDirection(stepIndex);
		else if (!STRUMMING_REST_SYMBOLS.has(character)) continue;
		steps.push({
			index: stepIndex,
			direction,
			breakBefore: breakBefore.has(stepIndex),
			sourceOffset
		});
		stepIndex += 1;
	}
	return steps;
}
function describeStrummingPatternStepDirection(direction) {
	if (direction === "down") return "down";
	if (direction === "up") return "up";
	return "none";
}
function renderStrummingPatternGrid(patternText, timeSignatureText, options = {}) {
	const timeSignature = getStrummingTimeSignatureDefinition(timeSignatureText);
	const steps = parseStrummingPatternSteps(patternText, options);
	const interactive = Boolean(options.interactive);
	const patternIndex = Number.isInteger(options.patternIndex) ? options.patternIndex : null;
	const patternLabel = String(options.patternLabel ?? "pattern").trim() || "pattern";
	if (!steps.length) return "";
	const countCells = steps.map((step) => {
		const label = getStrummingStepLabel(step.index, timeSignature);
		const classNames = ["ol-song-view__pattern-cell"];
		if (label.accent) classNames.push("ol-song-view__pattern-cell--accent");
		if (step.breakBefore) classNames.push("ol-song-view__pattern-cell--break");
		if (!interactive || patternIndex == null) return `<span class="${classNames.join(" ")}">${escapeHtml$1(label.text)}</span>`;
		const stateText = describeStrummingPatternStepDirection(step.direction);
		const stepLabel = label.text || String(step.index + 1);
		return `<button class="${classNames.join(" ")} ol-song-view__pattern-cell-button" type="button" data-preview-action="toggle-strumming-pattern-step" data-pattern-index="${escapeHtml$1(patternIndex)}" data-pattern-step-index="${escapeHtml$1(step.index)}" aria-label="${escapeHtml$1(`Toggle ${patternLabel} step ${stepLabel}. Current state: ${stateText}.`)}" title="${escapeHtml$1(`${patternLabel} ${stepLabel}: ${stateText}`)}">${escapeHtml$1(stepLabel)}</button>`;
	}).join("");
	const strokeCells = steps.map((step) => {
		const classNames = ["ol-song-view__pattern-cell", "ol-song-view__pattern-cell--stroke"];
		if (step.direction === "down") classNames.push("ol-song-view__pattern-cell--down");
		else if (step.direction === "up") classNames.push("ol-song-view__pattern-cell--up");
		else classNames.push("ol-song-view__pattern-cell--rest");
		if (step.breakBefore) classNames.push("ol-song-view__pattern-cell--break");
		const symbol = step.direction === "down" ? "&darr;" : step.direction === "up" ? "&uarr;" : "&nbsp;";
		return `<span class="${classNames.join(" ")}">${symbol}</span>`;
	}).join("");
	const beatGuideRow = renderStrummingBeatGuideRow(steps.length, timeSignature);
	return [
		`<div class="ol-song-view__pattern-display" style="--pattern-column-count: ${steps.length}">`,
		beatGuideRow,
		`<div class="ol-song-view__pattern-row ol-song-view__pattern-row--stroke">${strokeCells}</div>`,
		`<div class="ol-song-view__pattern-row ol-song-view__pattern-row--count">${countCells}</div>`,
		"</div>"
	].join("");
}
function renderStrummingPatternCards(patternLines, timeSignatureText, options = {}) {
	const patterns = Array.isArray(options.patterns) ? options.patterns : parseStrummingPatterns(patternLines, { allowZwspSeparators: options.allowZwspSeparators });
	const resolvedTimeSignatureText = String(timeSignatureText ?? "").trim() || "4/4";
	const sharedPatternDataAttributes = getStrummingPatternPreviewDataAttributes({
		keyText: options.keyText,
		tempoText: options.tempoText,
		timeSignatureText: resolvedTimeSignatureText
	});
	if (!patterns.length) return "";
	const containerClassName = options.containerClassName || "ol-song-view__pattern-grid";
	const cardClassName = options.cardClassName || "ol-song-view__pattern-card";
	return [
		`<div class="${escapeHtml$1(containerClassName)}"${sharedPatternDataAttributes}>`,
		...patterns.map((pattern, patternIndex) => {
			const editorDataAttributes = options.includeEditorData ? getEditorDataAttributes$1(pattern.lineNumber, pattern.column) : "";
			const patternIndexText = `#${patternIndex + 1}`;
			const usesFallbackLabel = String(pattern.label ?? "").trim() === `Pattern #${patternIndex + 1}`;
			const patternLabelText = usesFallbackLabel ? "" : pattern.label;
			const patternHeadingAriaLabel = usesFallbackLabel ? `${pattern.label}: ${pattern.pattern}` : `${patternIndexText} ${pattern.label}: ${pattern.pattern}`;
			const patternActionHtml = typeof options.renderPatternActions === "function" ? options.renderPatternActions(pattern, patternIndex) : "";
			const patternDataAttributes = [
				sharedPatternDataAttributes,
				` data-pattern-index="${escapeHtml$1(patternIndex)}"`,
				` data-pattern-label="${escapeHtml$1(pattern.label)}"`,
				` data-pattern-source="${escapeHtml$1(pattern.pattern)}"`
			].join("");
			const patternTargetId = createPatternPreviewTargetId(options.patternTargetIdPrefix, patternIndex + 1);
			return [
				`<section class="${escapeHtml$1(cardClassName)}"${patternTargetId ? ` id="${escapeHtml$1(patternTargetId)}"` : ""}${editorDataAttributes}${patternDataAttributes}>`,
				"<div class=\"ol-song-view__pattern-header\">",
				"<div class=\"ol-song-view__pattern-heading\">",
				`<h3 class="ol-song-view__pattern-title" title="${escapeHtml$1(pattern.pattern)}" aria-label="${escapeHtml$1(patternHeadingAriaLabel)}"><span class="ol-song-view__pattern-index">${escapeHtml$1(patternIndexText)}</span>${patternLabelText ? ` <span class="ol-song-view__pattern-label">${escapeHtml$1(patternLabelText)}</span>` : ""}</h3>`,
				"</div>",
				patternActionHtml,
				"</div>",
				renderStrummingPatternGrid(pattern.pattern, resolvedTimeSignatureText, {
					allowZwspSeparators: pattern.allowZwspSeparators,
					interactive: Boolean(options.includeStepActions),
					patternIndex,
					patternLabel: pattern.label
				}),
				"</section>"
			].join("");
		}),
		"</div>"
	].join("");
}
function renderStrummingPatternsAddAction() {
	return [
		"<div class=\"ol-preview-config__patterns-action\">",
		"<button class=\"ol-preview-config__part-action\" type=\"button\" data-preview-action=\"add-strumming-pattern\" aria-label=\"Add strumming pattern\" title=\"Add strumming pattern\">+</button>",
		"</div>"
	].join("");
}
function getStrummingPatternPreviewDataAttributes(options = {}) {
	const keyText = String(options.keyText ?? "").trim();
	const tempoText = String(options.tempoText ?? "").trim();
	const timeText = String(options.timeSignatureText ?? options.timeText ?? "").trim();
	const attributes = [];
	if (keyText) attributes.push(` data-pattern-preview-key="${escapeHtml$1(keyText)}"`);
	if (timeText) attributes.push(` data-pattern-preview-time="${escapeHtml$1(timeText)}"`);
	if (tempoText) attributes.push(` data-pattern-preview-tempo="${escapeHtml$1(tempoText)}"`);
	return attributes.join("");
}
function renderConfigStrummingPatternValue(patternLines, timeSignatureText, options = {}) {
	const patterns = Array.isArray(options.patterns) ? options.patterns : parseStrummingPatterns(patternLines, { allowZwspSeparators: options.allowZwspSeparators });
	const cardsHtml = renderStrummingPatternCards(patternLines, timeSignatureText, {
		cardClassName: "ol-song-view__pattern-card ol-preview-config__pattern-card",
		containerClassName: "ol-song-view__pattern-grid ol-preview-config__pattern-grid",
		includeEditorData: true,
		includeStepActions: true,
		keyText: options.keyText,
		patterns,
		patternTargetIdPrefix: options.patternPreviewTargetIdPrefix,
		tempoText: options.tempoText,
		renderPatternActions(pattern, patternIndex) {
			return [
				"<div class=\"ol-preview-config__pattern-actions\">",
				`<button class="ol-preview-config__pattern-duplicate" type="button" data-preview-action="duplicate-strumming-pattern" data-pattern-index="${escapeHtml$1(patternIndex)}" aria-label="Duplicate ${escapeHtml$1(pattern.label)}" title="Duplicate ${escapeHtml$1(pattern.label)}"><span class="ol-preview-config__pattern-duplicate-icon" aria-hidden="true"></span></button>`,
				`<button class="ol-preview-config__pattern-remove" type="button" data-preview-action="remove-strumming-pattern" data-pattern-index="${escapeHtml$1(patternIndex)}" aria-label="Remove ${escapeHtml$1(pattern.label)}" title="Remove ${escapeHtml$1(pattern.label)}">&times;</button>`,
				"</div>"
			].join("");
		}
	});
	return `<div class="ol-preview-config__patterns-value${patterns.length ? "" : " ol-preview-config__patterns-value--empty"}">${cardsHtml}${renderStrummingPatternsAddAction()}</div>`;
}
function createPreviewHelpers(viewOptions = {}) {
	const normalizedViewOptions = normalizePreviewViewOptions(viewOptions);
	return {
		createStrummingPatternPreviewContextFromConfigBody(configBody, options = {}) {
			return createStrummingPatternPreviewContextFromConfigBody(configBody, options);
		},
		createPreviewTargetId,
		createPreviewLineEntries(body, sourceLocation, allowZwspSeparators) {
			return createPreviewLineEntries(body, sourceLocation, allowZwspSeparators ?? shouldAllowInvisibleWordSeparators(body), normalizedViewOptions.showComments);
		},
		escapeHtml: escapeHtml$1,
		getEditorDataAttributes: getEditorDataAttributes$1,
		getFenceHeaderEditorDataAttributes,
		hasChordProgressionText,
		renderChordProgressionLineCollection(lines) {
			return renderChordProgressionLineCollection(lines, normalizedViewOptions);
		},
		renderConfigStrummingPatternValue(patternLines, timeSignatureText, options) {
			return renderConfigStrummingPatternValue(patternLines, timeSignatureText, {
				...options,
				patternPreviewTargetIdPrefix: options.patternPreviewTargetIdPrefix || normalizedViewOptions.patternPreviewTargetIdPrefix
			});
		},
		renderInlineText(value) {
			return renderInlineOlText(value, normalizedViewOptions);
		},
		renderEmptyBody: renderEmptyFenceBody,
		renderLineCollection(lines, options = {}) {
			return renderLineCollection(lines, {
				...options,
				viewOptions: normalizedViewOptions
			});
		},
		renderLyricLineCollection(lines) {
			return renderLyricLineCollection(lines, normalizedViewOptions);
		},
		renderMixedLineCollection(lines) {
			return renderMixedLineCollection(lines, normalizedViewOptions);
		},
		renderStrummingPatternCards,
		renderStructureValue,
		translateLabel(label) {
			return translatePreviewLabel(normalizedViewOptions.labels, label);
		}
	};
}
var previewHelpers = createPreviewHelpers();
function renderUnknownFenceHtml(info, body, sourceLocation = null, helpers = previewHelpers) {
	const lines = helpers.createPreviewLineEntries(body, sourceLocation);
	const header = info || "unknown";
	const kind = "unknown";
	const title = info ? `ol:${info}` : "ol";
	const targetId = createPreviewTargetId(title);
	const editorLine = sourceLocation?.bodyLineNumber || "";
	const editorColumn = sourceLocation?.bodyColumn || "";
	const titleEditorAttributes = getFenceHeaderEditorDataAttributes(sourceLocation?.startLineNumber || "");
	return [
		`<details class="ol-preview-fence ol-preview-fence--${escapeHtml$1(kind)}" data-ol-kind="${escapeHtml$1(kind)}" data-ol-header="${escapeHtml$1(header)}"${targetId ? ` id="${escapeHtml$1(targetId)}"` : ""}${getEditorDataAttributes$1(editorLine, editorColumn)} open>`,
		"<summary class=\"ol-preview-fence__summary\">",
		`<span class="ol-preview-fence__title"${titleEditorAttributes}>${escapeHtml$1(title)}</span>`,
		"</summary>",
		`<div class="ol-preview-fence__body">${helpers.renderLineCollection(lines)}</div>`,
		"</details>"
	].join("");
}
function renderOpenLyricFenceHtml(info, body, sourceLocation = null, helpers = previewHelpers) {
	const parsedHeader = parseFenceHeader(info);
	const definition = parsedHeader?.definition || null;
	if (!definition) return renderUnknownFenceHtml(info, body, sourceLocation, helpers);
	return definition.renderPreview({
		body,
		parsedHeader,
		sourceLocation,
		helpers
	});
}
/**
* What the markdown preview renders for a document with nothing in it.
*
* The markup belongs to the `Config` fence definition — the one part every
* song needs, and so the one a blank document starts from — so this only
* looks the definition up, the way `renderOpenLyricFenceHtml` does for a
* written fence.
*/
function renderOpenLyricEmptyDocumentHtml(helpers = previewHelpers) {
	return (parseFenceHeader("Config")?.definition || null)?.renderPreviewEmptyDocument?.({ helpers }) || "";
}
/**
* Unfold every Config extras disclosure inside `root` — the header's Theme,
* Genre, Style, Keywords, Year and Melody rows and its Attachments list.
*
* The panel renders them folded (`renderConfigExtras`), which is a reader's
* convenience — a picture of the song has nothing to click, so a printout, an
* export image, an exported HTML surface and the `Info` card all run this over
* the markup they were built from and show the facts the way the plain-text
* forms list them. The `<details>` becomes a plain block of the same class and
* its summary goes: merely opening it would still draw the toggle row, and an
* empty `<details>` would grow the browser's own "Details" label instead.
*/
function expandOpenLyricExtras(root) {
	if (!root || typeof root.querySelectorAll !== "function") return;
	root.querySelectorAll("details.ol-song-view__extras").forEach((element) => {
		const ownerDocument = element.ownerDocument;
		if (!ownerDocument || typeof element.replaceWith !== "function") {
			element.setAttribute("open", "");
			return;
		}
		const block = ownerDocument.createElement("div");
		block.className = element.className;
		Array.from(element.childNodes).forEach((child) => {
			if (child.nodeName !== "SUMMARY") block.append(child);
		});
		element.replaceWith(block);
	});
}
//#endregion
//#region src/plugins/OpenLyric/preview/index.ts
var BARE_CHORD_RE$1 = new RegExp(`^${CHORD_SYMBOL_SOURCE}$`);
var PLAIN_OL_TOKEN_RE = /(\{[^{}\r\n]+\}|\|\|:|\|:|:\|\||:\||\||\([1-9]\d*x\))/g;
var MIXED_SECTION_KINDS = /* @__PURE__ */ new Set([
	"intro",
	"outro",
	"turnaround"
]);
var OPEN_LYRIC_PATTERN_TARGET_ID_PREFIX = "ol-song-view-pattern";
var OPEN_LYRIC_INLINE_MARKDOWN_SELECTOR = [
	".ol-song-view__title",
	".ol-song-view__subtitle",
	".ol-song-view__copyright",
	".ol-song-view__description > span",
	".ol-song-view__detail-value > span",
	".ol-song-view__attachment > span"
].join(", ");
function normalizeNewlines$1(value) {
	return String(value ?? "").replace(/\r\n?/g, "\n");
}
function normalizeInlinePlainText(value) {
	return renderInlineTextPlainText(String(value ?? ""));
}
function renderInlineMarkdownFragment(text) {
	return sanitizeHtml(marked.parseInline(normalizeMarkdownRenderableUrls(text), {
		gfm: true,
		breaks: true
	}));
}
function renderOpenLyricInlineMarkdown(html) {
	const doc = new DOMParser().parseFromString(String(html ?? ""), "text/html");
	doc.querySelectorAll(OPEN_LYRIC_INLINE_MARKDOWN_SELECTOR).forEach((root) => {
		const source = root.textContent || "";
		if (!source.trim()) return;
		root.innerHTML = renderInlineMarkdownFragment(source);
	});
	return doc.body.innerHTML;
}
function transposeInlineChordText(text, semitoneOffset, targetKeyText) {
	return String(text ?? "").replace(/\[([^\[\]\r\n]+)\]/g, (_match, chordText) => {
		return `[${transposeChordSymbol(chordText, semitoneOffset, targetKeyText)}]`;
	});
}
function transposeChordProgressionSegment(text, semitoneOffset, targetKeyText) {
	return String(text ?? "").split(/(\s+)/).map((segment) => {
		if (!segment || /^\s+$/.test(segment)) return segment;
		return BARE_CHORD_RE$1.test(segment) ? transposeChordSymbol(segment, semitoneOffset, targetKeyText) : segment;
	}).join("");
}
function transposeChordProgressionText(text, semitoneOffset, targetKeyText) {
	const source = String(text ?? "");
	let transposedText = "";
	let lastIndex = 0;
	for (const match of source.matchAll(PLAIN_OL_TOKEN_RE)) {
		const matchIndex = match.index ?? 0;
		transposedText += transposeChordProgressionSegment(source.slice(lastIndex, matchIndex), semitoneOffset, targetKeyText);
		transposedText += match[0];
		lastIndex = matchIndex + match[0].length;
	}
	transposedText += transposeChordProgressionSegment(source.slice(lastIndex), semitoneOffset, targetKeyText);
	return transposedText;
}
/**
* Should this line be read as a progression rather than a chorded lyric?
*
* `Instrumental` is progression by definition. The mixed sections (`Intro`,
* `Outro`) have to be asked line by line, because either kind of line may
* appear in them — reading a sung line as a progression would transpose the
* words that happen to spell chords.
*/
function isProgressionSectionText(text, sectionKind) {
	return sectionKind === "instrumental" || hasChordProgressionText(text) || MIXED_SECTION_KINDS.has(sectionKind) && isProgressionLineText(text);
}
function transposeSectionText(text, sectionKind, transposition) {
	if (!transposition?.isActive) return String(text ?? "");
	if (isProgressionSectionText(text, sectionKind)) return transposeChordProgressionText(text, transposition.semitoneOffset, transposition.targetKeyText);
	return transposeInlineChordText(text, transposition.semitoneOffset, transposition.targetKeyText);
}
function simplifyInlineChordText(text) {
	return String(text ?? "").replace(/\[([^\[\]\r\n]+)\]/g, (_match, chordText) => {
		return `[${simplifyChordSymbol(chordText)}]`;
	});
}
function simplifyChordProgressionSegment(text) {
	return String(text ?? "").split(/(\s+)/).map((segment) => {
		if (!segment || /^\s+$/.test(segment)) return segment;
		return BARE_CHORD_RE$1.test(segment) ? simplifyChordSymbol(segment) : segment;
	}).join("");
}
function simplifyChordProgressionText(text) {
	const source = String(text ?? "");
	let simplifiedText = "";
	let lastIndex = 0;
	for (const match of source.matchAll(PLAIN_OL_TOKEN_RE)) {
		const matchIndex = match.index ?? 0;
		simplifiedText += simplifyChordProgressionSegment(source.slice(lastIndex, matchIndex));
		simplifiedText += match[0];
		lastIndex = matchIndex + match[0].length;
	}
	simplifiedText += simplifyChordProgressionSegment(source.slice(lastIndex));
	return simplifiedText;
}
function simplifySectionText(text, sectionKind) {
	if (isProgressionSectionText(text, sectionKind)) return simplifyChordProgressionText(text);
	return simplifyInlineChordText(text);
}
function createDeclaredPartMap(fences) {
	const parts = /* @__PURE__ */ new Map();
	fences.forEach((fence) => {
		const partName = fence.parsedHeader.partName;
		if (!partName || partName === "Config") return;
		if (!parts.has(partName)) parts.set(partName, fence);
	});
	return parts;
}
function parseStructureSteps(structureEntry) {
	if (!structureEntry) return [];
	const primaryValue = structureEntry.values.find((value) => String(value.text ?? "").trim()) || structureEntry.values[0] || null;
	if (!primaryValue) return [];
	const parsedStructure = parseStructureValue(primaryValue.text);
	if (parsedStructure.error) return [];
	return parsedStructure.steps.map((step, stepIndex) => ({
		...step,
		sectionIndex: stepIndex + 1,
		sectionTotal: parsedStructure.steps.length,
		editorLine: primaryValue.lineEntry.lineNumber,
		editorColumn: (primaryValue.valueColumn || primaryValue.lineEntry.column) + step.startOffset
	}));
}
/**
* The `partNameFilter` view option: the one section (part) name a render is
* scoped to, or `''` for the whole song. Callers that only need one section —
* `getValue({ key })` / `getElementMap({ key })` on the component — pass it so
* the pipeline never builds the rest of the song.
*/
function normalizePartNameFilter(options) {
	return String(options?.partNameFilter ?? "").trim();
}
/**
* The structure steps a `partNameFilter` keeps: the FIRST step naming that
* part, so a part repeated in the flow (`IV1CV2CO` plays Chorus twice) renders
* once — the same uniqueness the section maps have. Empty when the name is not
* in the structure at all, which renders nothing rather than the whole song.
*/
/**
* The song's notes the flow does not place: one step per `ol:Note` fence the
* Structure leaves out, in the order the notes are written. A note the
* Structure names is sung (or read) where it stands, like any section; the
* others gather at the bottom of the song — unless `hideNotes` leaves them
* out — so a note never shows twice. They carry no place in the flow, so
* their cards have no index badge.
*/
function listUnplacedNoteSteps(partMap, steps, options = {}) {
	if (options.hideNotes) return [];
	const placed = new Set(steps.map((step) => step.partName || step.partText));
	const notes = [];
	partMap.forEach((fence, partName) => {
		if (fence?.parsedHeader?.header === "Note" && !placed.has(partName)) notes.push({
			partName,
			partText: partName,
			isUnplacedNote: true
		});
	});
	return notes;
}
function filterStepsByPartName(steps, partNameFilter) {
	if (!partNameFilter) return steps;
	const match = steps.find((step) => (step.partName || step.partText) === partNameFilter);
	return match ? [match] : [];
}
function parseConfigEntries(configFence) {
	if (!configFence) return [];
	const entries = [];
	let currentEntry = null;
	for (const lineEntry of createPreviewLineEntries(configFence.body, { startLineNumber: configFence.startLineNumber })) {
		const line = lineEntry.text;
		if (!line.trim()) continue;
		const fieldMatch = line.match(/^\s*-\s*([^:]+):\s*(.*)$/);
		if (fieldMatch) {
			const separatorOffset = line.indexOf(":");
			const valueOffset = separatorOffset === -1 ? line.length : separatorOffset + 1;
			const valueIndentLength = line.slice(valueOffset).match(/^\s*/)?.[0].length || 0;
			currentEntry = {
				key: normalizeConfigFieldName(fieldMatch[1]),
				lineEntry,
				values: [{
					text: fieldMatch[2],
					lineEntry,
					valueColumn: valueOffset + valueIndentLength + 1
				}]
			};
			entries.push(currentEntry);
			continue;
		}
		if (currentEntry) currentEntry.values.push({
			text: line.trim(),
			lineEntry,
			valueColumn: lineEntry.column
		});
	}
	return entries;
}
function createConfigEntryMap(entries) {
	return new Map(entries.map((entry) => [entry.key, entry]));
}
function getPlainTextConfigValueLines(entryMap, key) {
	const entry = entryMap.get(key);
	if (!entry) return [];
	return entry.values.map((value) => normalizeInlinePlainText(value.text).trim()).filter(Boolean);
}
function getPlainTextConfigValue(entryMap, key) {
	return getPlainTextConfigValueLines(entryMap, key).join(" ");
}
function getConfigValueLines(entryMap, key) {
	const entry = entryMap.get(key);
	if (!entry) return [];
	return entry.values.map((value) => String(value.text ?? "").trim()).filter(Boolean);
}
function getConfigValue(entryMap, key) {
	return getConfigValueLines(entryMap, key).join(" ");
}
function renderTextBlock(lines) {
	if (!lines.length) return "";
	return lines.map((line) => `<span>${previewHelpers.escapeHtml(line)}</span>`).join("<br>");
}
function renderMetaEntryValue(field, value, labels = null) {
	const escapedField = previewHelpers.escapeHtml(translatePreviewLabel(labels, field));
	const escapedValue = previewHelpers.escapeHtml(value);
	if (field !== "Key") return `<span class="ol-song-view__meta-entry"><strong>${escapedField}:</strong> ${escapedValue}</span>`;
	const chordTitle = previewHelpers.escapeHtml(describeChordKey(value));
	return `<span class="ol-song-view__meta-entry"><strong>${escapedField}:</strong> <button class="ol-preview-chord ol-song-view__meta-chord" type="button" data-chord-key="${escapedValue}" data-chord-title="${chordTitle}" aria-label="Show ${chordTitle}" title="Show ${chordTitle}">${escapedValue}</button></span>`;
}
function createMetaSummaryEntries(entryMap, options = {}) {
	const keyOverride = normalizeStructureKeyOption(options.keyTextOverride);
	return [
		"Key",
		"Time",
		"Tempo"
	].map((field) => {
		const value = field === "Key" ? keyOverride || getConfigValue(entryMap, field) : getConfigValue(entryMap, field);
		if (!value) return null;
		return {
			field,
			value
		};
	}).filter(Boolean);
}
function createPlainTextMetaSummaryEntries(entryMap, options = {}) {
	const keyOverride = normalizeStructureKeyOption(options.keyTextOverride);
	return [
		"Key",
		"Time",
		"Tempo"
	].map((field) => {
		const value = field === "Key" ? keyOverride || getPlainTextConfigValue(entryMap, field) : getPlainTextConfigValue(entryMap, field);
		if (!value) return null;
		return {
			field,
			value
		};
	}).filter(Boolean);
}
function renderMetaSummary(entryMap, options = {}) {
	const items = createMetaSummaryEntries(entryMap, options).map(({ field, value }) => {
		return renderMetaEntryValue(field, value, options.labels);
	});
	if (!items.length) return "";
	return `<div class="ol-song-view__meta-line">${items.join("<span class=\"ol-song-view__meta-separator\">&middot;</span>")}</div>`;
}
function renderReadOnlyStructureValue(values) {
	if (!Array.isArray(values) || !values.length) return "";
	if (values.length !== 1) return values.map((value) => {
		return `<span${previewHelpers.getEditorDataAttributes(value.lineEntry?.lineNumber, value.valueColumn || value.lineEntry?.column)}>${previewHelpers.renderInlineText(value.text)}</span>`;
	}).join("<br>");
	const [value] = values;
	const parsedStructure = parseStructureValue(value.text);
	const editorLine = value.lineEntry?.lineNumber;
	const baseColumn = value.valueColumn || value.lineEntry?.column || 1;
	if (parsedStructure.error) return `<span${previewHelpers.getEditorDataAttributes(editorLine, baseColumn)}>${previewHelpers.renderInlineText(value.text)}</span>`;
	if (!parsedStructure.steps.length) return "";
	return `<div class="ol-song-view__structure-overview-value"><div class="ol-preview-structure-line">${parsedStructure.steps.map((step, index) => {
		const targetId = step.parsedHeader ? createSongViewTargetId(step.partName) : "";
		const editorColumn = baseColumn + step.startOffset;
		const stepAttributes = `${previewHelpers.getEditorDataAttributes(editorLine, editorColumn)}${step.header ? ` data-ol-header="${previewHelpers.escapeHtml(step.header)}"` : ""}`;
		const labelHtml = previewHelpers.renderInlineText(formatStructureStepLabel(step));
		return [
			"<span class=\"ol-preview-structure-link\">",
			targetId ? `<a class="ol-preview-structure-step" href="#${previewHelpers.escapeHtml(targetId)}" data-preview-target-id="${previewHelpers.escapeHtml(targetId)}"${stepAttributes}>${labelHtml}</a>` : `<span class="ol-preview-structure-step"${stepAttributes}>${labelHtml}</span>`,
			index < parsedStructure.steps.length - 1 ? "<span class=\"ol-preview-structure-arrow\" aria-hidden=\"true\">&rarr;</span>" : "",
			"</span>"
		].join("");
	}).join("")}</div></div>`;
}
function renderPatternCards(entryMap, options = {}) {
	if (options.hideStrummingPatterns) return "";
	const originalKeyText = getConfigValue(entryMap, "Key");
	const keyText = normalizeStructureKeyOption(options.selectedStructureKeys?.["config-structure"]) || parseMainKey(originalKeyText)?.raw || originalKeyText;
	return previewHelpers.renderStrummingPatternCards(getConfigValueLines(entryMap, "Strumming Patterns"), getConfigValue(entryMap, "Time") || "4/4", {
		keyText,
		tempoText: getConfigValue(entryMap, "Tempo"),
		patterns: options.patternPreviewContext?.patterns,
		patternTargetIdPrefix: OPEN_LYRIC_PATTERN_TARGET_ID_PREFIX
	});
}
function formatRepeatText(repeatText) {
	return String(repeatText ?? "").trim().replace(/^\((.*)\)$/, "$1");
}
var CONFIG_DETAIL_FIELDS = [
	"Theme",
	"Genre",
	"Style",
	"Keywords",
	"Year",
	"Melody"
];
function renderConfigDetailRows(entryMap, options = {}) {
	const fields = [];
	const rows = [];
	CONFIG_DETAIL_FIELDS.forEach((field) => {
		const valueLines = getConfigValueLines(entryMap, field);
		if (!valueLines.length) return;
		const label = translatePreviewLabel(options.labels, field);
		fields.push(label);
		rows.push([
			"<div class=\"ol-song-view__detail\">",
			`<span class="ol-song-view__detail-label">${previewHelpers.escapeHtml(label)}:</span>`,
			`<span class="ol-song-view__detail-value">${renderTextBlock(valueLines)}</span>`,
			"</div>"
		].join(""));
	});
	return {
		fields,
		html: rows.length ? `<div class="ol-song-view__details">${rows.join("")}</div>` : ""
	};
}
function renderConfigAttachments(entryMap, options = {}) {
	if (options.hideAttachments) return {
		count: 0,
		html: ""
	};
	const attachmentLines = getConfigValueLines(entryMap, "Attachments");
	if (!attachmentLines.length) return {
		count: 0,
		html: ""
	};
	const items = attachmentLines.map((line) => `<li class="ol-song-view__attachment"><span>${previewHelpers.escapeHtml(line)}</span></li>`).join("");
	return {
		count: attachmentLines.length,
		html: [
			"<div class=\"ol-song-view__attachments\">",
			`<span class="ol-song-view__detail-label">${previewHelpers.escapeHtml(translatePreviewLabel(options.labels, "Attachments"))}:</span>`,
			`<ul class="ol-song-view__attachment-list">${items}</ul>`,
			"</div>"
		].join("")
	};
}
function renderConfigExtras(entryMap, options = {}) {
	const details = renderConfigDetailRows(entryMap, options);
	const attachments = renderConfigAttachments(entryMap, options);
	if (!details.html && !attachments.html) return "";
	return [
		"<details class=\"ol-song-view__extras\">",
		"<summary class=\"ol-song-view__extras-summary\">",
		`<span class="ol-song-view__extras-items">${[...details.fields.map((field) => `<span class="ol-song-view__extras-item">${previewHelpers.escapeHtml(field)}</span>`), ...attachments.count ? [`<span class="ol-song-view__extras-item">${previewHelpers.escapeHtml(translatePreviewLabel(options.labels, "Attachments"))} <span class="ol-song-view__extras-count">(${attachments.count})</span></span>`] : []].join("<span class=\"ol-song-view__extras-separator\" aria-hidden=\"true\">·</span>")}</span>`,
		"</summary>",
		"<div class=\"ol-song-view__extras-body\">",
		details.html,
		attachments.html,
		"</div>",
		"</details>"
	].join("");
}
function renderConfigHeaderMeta(entryMap, options = {}) {
	const patternsHtml = renderPatternCards(entryMap, options);
	const descriptionLines = getConfigValueLines(entryMap, "Description");
	const copyrightText = getConfigValue(entryMap, "Copyright");
	const proseHtml = [descriptionLines.length ? `<div class="ol-song-view__description">${renderTextBlock(descriptionLines)}</div>` : "", copyrightText ? `<p class="ol-song-view__copyright">${previewHelpers.escapeHtml(copyrightText)}</p>` : ""].filter(Boolean).join("");
	const factsHtml = renderConfigExtras(entryMap, options);
	const groups = [
		patternsHtml ? `<div class="ol-song-view__header-group ol-song-view__header-group--patterns">${patternsHtml}</div>` : "",
		proseHtml ? `<div class="ol-song-view__header-group ol-song-view__header-group--prose">${proseHtml}</div>` : "",
		factsHtml ? `<div class="ol-song-view__header-group ol-song-view__header-group--facts">${factsHtml}</div>` : ""
	].filter(Boolean);
	if (!groups.length) return "";
	return `<div class="ol-song-view__header-meta">${groups.join("")}</div>`;
}
function renderConfigHeader(entryMap, options = {}) {
	const title = getConfigValue(entryMap, "Title") || translatePreviewLabel(options.labels, "Untitled Song");
	const secondaryText = [getConfigValue(entryMap, "Subtitle"), getConfigValue(entryMap, "Artist")].filter(Boolean).join(" · ");
	return [
		"<header class=\"ol-song-view__header\">",
		"<div class=\"ol-song-view__headline\">",
		`<h4 class="ol-song-view__title">${previewHelpers.escapeHtml(title)}</h4>`,
		secondaryText ? `<p class="ol-song-view__subtitle">${previewHelpers.escapeHtml(secondaryText)}</p>` : "",
		"</div>",
		renderConfigHeaderMeta(entryMap, options),
		"</header>"
	].join("");
}
function createSectionRenderContext(fence, transposition = null, options = {}) {
	const sourceLocation = getPreviewSourceLocation(fence.body, fence.startLineNumber);
	const simplifyChords = Boolean(options.simplifyChords);
	return {
		fence,
		sourceLocation,
		lineEntries: createPreviewLineEntries(fence.body, sourceLocation, void 0, Boolean(options.showComments)).map((lineEntry) => {
			if (lineEntry.isComment) return lineEntry;
			const transposedText = transposeSectionText(lineEntry.text, fence.parsedHeader.kind, transposition);
			return {
				...lineEntry,
				text: simplifyChords ? simplifySectionText(transposedText, fence.parsedHeader.kind) : transposedText
			};
		})
	};
}
/**
* The section's entries minus its comments — what everything *except* the
* rendered body must read.
*
* Comments are a preview-only authoring aid, so they may not change how a
* section is laid out (inline vs block) and may not reach the plain-text
* render the Copy as Text / PowerPoint / DOCX exports are built from.
*/
function getContentLineEntries(sectionContext) {
	const lineEntries = sectionContext?.lineEntries || [];
	return lineEntries.some((lineEntry) => lineEntry.isComment) ? lineEntries.filter((lineEntry) => !lineEntry.isComment) : lineEntries;
}
function renderSectionBody(sectionContext, sectionPreviewHelpers = previewHelpers) {
	const { fence, sourceLocation, lineEntries } = sectionContext;
	return fence.parsedHeader.definition.renderPreviewBody({
		body: fence.body,
		header: fence.parsedHeader.header,
		helpers: sectionPreviewHelpers,
		kind: fence.parsedHeader.kind,
		lineEntries,
		lines: getContentLineEntries(sectionContext).map((entry) => entry.text),
		parsedHeader: fence.parsedHeader,
		sourceLocation,
		targetId: createSongViewTargetId(fence.parsedHeader.partName),
		title: fence.parsedHeader.partName
	});
}
function isProgressionSection(sectionContext) {
	const { kind } = sectionContext.fence.parsedHeader;
	if (kind === "instrumental") return true;
	if (!MIXED_SECTION_KINDS.has(kind)) return false;
	const contentLineEntries = getContentLineEntries(sectionContext);
	return contentLineEntries.length === 1 && isProgressionSectionText(contentLineEntries[0]?.text, kind);
}
function hasInlineKeyMarkers(text) {
	return /(\[[^\[\]\r\n]+\]|\{[^{}\r\n]+\}|\|\|:|\|:|:\|\||:\||\|)/.test(String(text ?? ""));
}
function isInlinePlainTextSection(sectionContext) {
	const contentLineEntries = getContentLineEntries(sectionContext);
	if (contentLineEntries.length !== 1) return false;
	const text = String(contentLineEntries[0]?.text ?? "").trim();
	return Boolean(text) && !hasInlineKeyMarkers(text);
}
function getSongSectionDataAttributes(parsedHeader) {
	if (!parsedHeader) return "";
	const attributes = [];
	if (parsedHeader.kind) attributes.push(`data-ol-kind="${previewHelpers.escapeHtml(parsedHeader.kind)}"`);
	if (parsedHeader.header) attributes.push(`data-ol-header="${previewHelpers.escapeHtml(parsedHeader.header)}"`);
	return attributes.length ? ` ${attributes.join(" ")}` : "";
}
function getSongSectionTitleEditorDataAttributes(fence) {
	return previewHelpers.getFenceHeaderEditorDataAttributes(fence?.startLineNumber || "");
}
function getSongSectionRangeDataAttributes(fence) {
	if (!fence?.startLineNumber || !fence?.endLineNumber) return "";
	return ` data-preview-start-line="${previewHelpers.escapeHtml(fence.startLineNumber)}" data-preview-end-line="${previewHelpers.escapeHtml(fence.endLineNumber)}"`;
}
function getSongSectionPartDataAttributes(partName) {
	const normalizedPartName = String(partName ?? "").trim();
	if (!normalizedPartName) return "";
	return ` data-ol-part-name="${previewHelpers.escapeHtml(normalizedPartName)}"`;
}
function getMissingSectionTitleEditorDataAttributes(step) {
	return previewHelpers.getEditorDataAttributes(step?.editorLine || "", step?.editorColumn || 1);
}
/**
* The section's 1-based position in the song flow — the same ordinal the
* structure chips above the sections count off, so `Chorus` sung twice is 3 and
* 5 rather than one number used twice. Stamped on the step by
* {@link parseStructureSteps}.
*
* It is written into the markup rather than drawn by a CSS counter because a
* section is not always rendered inside the sections grid: the image export
* lifts each one into its own tile (`wrapInSectionTile` in
* `src/editor/components/OpenLyric.ts`), and a counter would restart at 1 there.
*/
function getSongSectionIndex(step) {
	const sectionIndex = Number(step?.sectionIndex);
	return Number.isInteger(sectionIndex) && sectionIndex > 0 ? sectionIndex : 0;
}
/**
* How many steps the whole flow has, carried beside the index so a reader of
* the markup can say `3/6` without the rest of the song in hand — which is
* exactly the position a section rendered on its own is in (a tile in the
* element map, one re-rendered fence). See
* {@link OpenLyricElementMapOptions.isShowingTotalIndex} on the component.
*/
function getSongSectionTotal(step) {
	const sectionTotal = Number(step?.sectionTotal);
	return Number.isInteger(sectionTotal) && sectionTotal > 0 ? sectionTotal : 0;
}
function getSongSectionIndexDataAttributes(sectionIndex, sectionTotal) {
	if (!sectionIndex) return "";
	return ` data-ol-section-index="${sectionIndex}"` + (sectionTotal ? ` data-ol-section-total="${sectionTotal}"` : "");
}
function renderSongSectionIndex(sectionIndex) {
	if (!sectionIndex) return "";
	return `<span class="ol-song-view__section-index" aria-hidden="true">${sectionIndex}</span>`;
}
function renderMissingSection(step) {
	const sectionIndex = getSongSectionIndex(step);
	const sectionTotal = getSongSectionTotal(step);
	const partName = step.partName || step.partText;
	const repeatText = formatRepeatText(step.repeatText);
	const sectionDataAttributes = getSongSectionDataAttributes(step.parsedHeader);
	const sectionTargetId = createSongViewTargetId(partName);
	const titleEditorAttributes = getMissingSectionTitleEditorDataAttributes(step);
	return [
		`<section class="ol-song-view__section ol-song-view__section--missing"${sectionTargetId ? ` id="${previewHelpers.escapeHtml(sectionTargetId)}"` : ""}${sectionDataAttributes}${getSongSectionPartDataAttributes(partName)}${getSongSectionIndexDataAttributes(sectionIndex, sectionTotal)}>`,
		renderSongSectionIndex(sectionIndex),
		"<div class=\"ol-song-view__section-line\">",
		`<h2 class="ol-song-view__section-title"${titleEditorAttributes}>${previewHelpers.escapeHtml(partName)}:</h2>`,
		repeatText ? `<span class="ol-preview-repeat ol-song-view__repeat">${previewHelpers.escapeHtml(repeatText)}</span>` : "",
		"</div>",
		`<div class="ol-song-view__section-body"><div class="ol-song-view__missing-note">Missing declared part for ${previewHelpers.escapeHtml(partName)}.</div></div>`,
		"</section>"
	].join("");
}
function renderSongSection(step, partMap, transposition = null, options = {}) {
	const partName = step.partName || step.partText;
	const fence = partMap.get(partName);
	if (!fence) return renderMissingSection(step);
	const sectionIndex = getSongSectionIndex(step);
	const sectionTotal = getSongSectionTotal(step);
	const sectionContext = createSectionRenderContext(fence, transposition, options);
	const sectionBody = renderSectionBody(sectionContext, options.previewHelpers || previewHelpers);
	const repeatText = formatRepeatText(step.repeatText);
	const inlineProgression = isProgressionSection(sectionContext) && getContentLineEntries(sectionContext).length === 1;
	const inlinePlainText = isInlinePlainTextSection(sectionContext);
	const inlineSection = inlineProgression || inlinePlainText;
	const sectionDataAttributes = getSongSectionDataAttributes(fence.parsedHeader);
	const sectionTargetId = createSongViewTargetId(partName);
	const titleEditorAttributes = getSongSectionTitleEditorDataAttributes(fence);
	return [
		`<section class="${[
			"ol-song-view__section",
			inlineSection ? "ol-song-view__section--inline" : "",
			step.isUnplacedNote ? "ol-song-view__section--note" : ""
		].filter(Boolean).join(" ")}"${sectionTargetId ? ` id="${previewHelpers.escapeHtml(sectionTargetId)}"` : ""}${sectionDataAttributes}${getSongSectionPartDataAttributes(partName)}${getSongSectionRangeDataAttributes(fence)}${getSongSectionIndexDataAttributes(sectionIndex, sectionTotal)}>`,
		renderSongSectionIndex(sectionIndex),
		`<div class="ol-song-view__section-line${inlineProgression ? " ol-song-view__section-line--inline" : ""}${inlinePlainText ? " ol-song-view__section-line--inline-text" : ""}">`,
		`<h2 class="ol-song-view__section-title"${titleEditorAttributes}>${previewHelpers.escapeHtml(partName)}:</h2>`,
		repeatText ? `<span class="ol-preview-repeat ol-song-view__repeat">${previewHelpers.escapeHtml(repeatText)}</span>` : "",
		inlineSection ? `<div class="ol-song-view__section-inline-body${inlinePlainText ? " ol-song-view__section-inline-body--text" : ""}">${sectionBody}</div>` : "",
		"</div>",
		inlineSection ? "" : `<div class="ol-song-view__section-body">${sectionBody}</div>`,
		"</section>"
	].join("");
}
function renderSongSections(steps, partMap, transposition = null, options = {}) {
	const sectionPreviewHelpers = options.previewHelpers || previewHelpers;
	if (!steps.length) return "<div class=\"ol-song-view__empty\">Add a valid - Structure: code to ol:Config to render the song flow.</div>";
	return [
		"<div class=\"ol-song-view__sections\">",
		...steps.map((step) => renderSongSection(step, partMap, transposition, {
			...options,
			previewHelpers: sectionPreviewHelpers
		})),
		"</div>"
	].join("");
}
/**
* The notes the flow leaves out, as cards in a grid of their own — behind a
* labelled divider (`withDivider`) when they follow the song's sections, so a
* reader does not take them for one more part of the Structure. A render scoped
* to one note has no flow above it to split from, and no divider.
*/
function renderNoteSections(noteSteps, partMap, transposition, options = {}) {
	if (!noteSteps.length) return "";
	return [
		options.withDivider ? "<div class=\"ol-song-view__notes-divider\" role=\"separator\" aria-label=\"Song notes\"><span class=\"ol-song-view__notes-divider-label\" data-ol-translate=\"\">Song notes</span></div>" : "",
		"<div class=\"ol-song-view__sections ol-song-view__notes\">",
		...noteSteps.map((step) => renderSongSection(step, partMap, transposition, options)),
		"</div>"
	].join("");
}
function trimPlainTextLines(lines) {
	const normalizedLines = Array.isArray(lines) ? lines.map((line) => String(line ?? "").replace(/\s+$/g, "")) : [];
	let startIndex = 0;
	let endIndex = normalizedLines.length;
	while (startIndex < endIndex && !String(normalizedLines[startIndex] ?? "").trim()) startIndex += 1;
	while (endIndex > startIndex && !String(normalizedLines[endIndex - 1] ?? "").trim()) endIndex -= 1;
	return normalizedLines.slice(startIndex, endIndex);
}
function getSectionPlainTextBodyLines(sectionContext, options = {}) {
	const bodyLines = trimPlainTextLines(getContentLineEntries(sectionContext).map((lineEntry) => lineEntry.text)).map((line) => normalizeInlinePlainText(line).trimStart());
	if (!options.hideBracketedKeys) return bodyLines;
	return trimPlainTextLines(bodyLines.filter((line) => !isChordOnlyLineText(line)));
}
function formatPlainTextRepeatSuffix(repeatText) {
	const normalizedRepeatText = formatRepeatText(repeatText);
	return normalizedRepeatText ? ` (${normalizedRepeatText})` : "";
}
function createMissingSectionPlainTextData(step) {
	const partName = step.partName || step.partText || "Untitled Part";
	return {
		partName,
		repeatText: formatRepeatText(step.repeatText),
		heading: `${partName}:${formatPlainTextRepeatSuffix(step.repeatText)}`,
		isInline: false,
		lineGroups: [[`Missing declared part for ${partName}.`]]
	};
}
function createSongSectionPlainTextData(sectionContext, step, options = {}) {
	const partName = step.partName || step.partText || "Untitled Part";
	const repeatText = formatRepeatText(step.repeatText);
	const heading = `${partName}:${formatPlainTextRepeatSuffix(step.repeatText)}`;
	const bodyLines = getSectionPlainTextBodyLines(sectionContext, options);
	const inlineProgression = isProgressionSection(sectionContext) && bodyLines.length === 1;
	const inlinePlainText = isInlinePlainTextSection(sectionContext) && bodyLines.length === 1;
	if (!bodyLines.length) return {
		partName,
		repeatText,
		heading,
		isInline: false,
		lineGroups: []
	};
	if (inlineProgression || inlinePlainText) return {
		partName,
		repeatText,
		heading,
		isInline: true,
		lineGroups: [[bodyLines[0]]]
	};
	return {
		partName,
		repeatText,
		heading,
		isInline: false,
		lineGroups: bodyLines.map((line) => {
			if (!line) return [""];
			return createChordedLyricTextLines(line, {
				hideBracketedKeys: Boolean(options.hideBracketedKeys),
				hideLeadingBars: Boolean(options.hideLeadingBars)
			});
		})
	};
}
function renderSongSectionPlainTextData(sectionData) {
	if (!sectionData) return "";
	const lines = (Array.isArray(sectionData.lineGroups) ? sectionData.lineGroups : []).flatMap((group) => {
		if (!Array.isArray(group) || !group.length) return [""];
		return group.map((line) => String(line ?? ""));
	});
	if (!lines.length) return sectionData.heading;
	if (sectionData.isInline && lines.length === 1) return `${sectionData.heading} ${lines[0]}`;
	return [sectionData.heading, ...lines.map((line) => {
		if (!line) return "";
		return `  ${line}`;
	})].join("\n");
}
function createSongSectionsPlainTextData(steps, partMap, transposition = null, options = {}) {
	if (!steps.length) return [];
	return steps.map((step) => {
		const partName = step.partName || step.partText;
		const fence = partMap.get(partName);
		if (!fence) return createMissingSectionPlainTextData(step);
		return createSongSectionPlainTextData(createSectionRenderContext(fence, transposition, options), step, options);
	});
}
function createPlainTextStructureLine(structureEntry, parsedSteps = null) {
	const steps = Array.isArray(parsedSteps) ? parsedSteps : parseStructureSteps(structureEntry);
	if (steps.length) return `Structure: ${steps.map((step) => step.partName || step.partText || "Untitled Part").join(" - ")}`;
	const rawStructureValue = Array.isArray(structureEntry?.values) ? structureEntry.values.map((value) => normalizeInlinePlainText(value.text).trim()).filter(Boolean).join(" ") : "";
	return rawStructureValue ? `Structure: ${rawStructureValue}` : "";
}
function createPlainTextStrummingPatternLines(entryMap, options = {}) {
	const entry = entryMap.get("Strumming Patterns");
	if (!entry) return [];
	const patterns = (Array.isArray(options.patterns) ? options.patterns : parseStrummingPatterns(entry.values.map((value) => ({
		...value,
		text: normalizeInlinePlainText(value.text)
	})))).map((pattern) => ({
		...pattern,
		label: normalizeInlinePlainText(pattern.label).trim(),
		pattern: normalizeStrummingPatternValue(normalizeInlinePlainText(pattern.pattern), pattern.allowZwspSeparators).trim()
	}));
	if (patterns.length === 1 && !Number.isInteger(patterns[0].labelSourceIndex)) return [`Strumming Pattern: ${patterns[0].pattern}`];
	if (patterns.length) return ["Strumming Patterns:", ...patterns.filter((pattern) => pattern.pattern).map((pattern) => {
		return `  ${pattern.label ? `${pattern.label}: ${pattern.pattern}` : pattern.pattern}`;
	})];
	const rawLines = getPlainTextConfigValueLines(entryMap, "Strumming Patterns").map((line) => normalizeStrummingPatternValue(line).trim()).filter(Boolean);
	if (!rawLines.length) return [];
	if (rawLines.length === 1) return [`Strumming Pattern: ${rawLines[0]}`];
	return ["Strumming Patterns:", ...rawLines.map((line) => `  ${line}`)];
}
function createPlainTextConfigFieldBlock(field, valueLines, { alwaysExpanded = false } = {}) {
	const normalizedLines = Array.isArray(valueLines) ? valueLines.map((line) => String(line ?? "").trim()).filter(Boolean) : [];
	if (!normalizedLines.length) return [];
	if (!alwaysExpanded && normalizedLines.length === 1) return [`- ${field}: ${normalizedLines[0]}`];
	return [`- ${field}:`, ...normalizedLines.map((line) => `  ${line}`)];
}
function createPlainTextAdditionalConfigLines(entryMap, options = {}) {
	const descriptionLines = getPlainTextConfigValueLines(entryMap, "Description");
	const copyrightText = getPlainTextConfigValue(entryMap, "Copyright");
	const themeText = getPlainTextConfigValue(entryMap, "Theme");
	const genreText = getPlainTextConfigValue(entryMap, "Genre");
	const styleText = getPlainTextConfigValue(entryMap, "Style");
	const keywordsText = getPlainTextConfigValue(entryMap, "Keywords");
	const yearText = getPlainTextConfigValue(entryMap, "Year");
	const melodyText = getPlainTextConfigValue(entryMap, "Melody");
	const attachmentLines = options.hideAttachments ? [] : getPlainTextConfigValueLines(entryMap, "Attachments");
	return [
		...createPlainTextConfigFieldBlock("Description", descriptionLines),
		...copyrightText ? [`- Copyright: ${copyrightText}`] : [],
		...themeText ? [`- Theme: ${themeText}`] : [],
		...genreText ? [`- Genre: ${genreText}`] : [],
		...styleText ? [`- Style: ${styleText}`] : [],
		...keywordsText ? [`- Keywords: ${keywordsText}`] : [],
		...yearText ? [`- Year: ${yearText}`] : [],
		...melodyText ? [`- Melody: ${melodyText}`] : [],
		...createPlainTextConfigFieldBlock("Attachments", attachmentLines, { alwaysExpanded: true })
	];
}
function createOpenLyricPresentationData(markdown, options = {}) {
	const fences = parseOpenLyricFences(markdown);
	const configFence = fences.find((fence) => fence.parsedHeader.header === "Config") || null;
	if (!configFence) return null;
	const configEntries = createConfigEntryMap(parseConfigEntries(configFence));
	const patternPreviewContext = createStrummingPatternPreviewContextFromConfigBody(configFence.body);
	const partMap = createDeclaredPartMap(fences);
	const structureEntry = configEntries.get("Structure") || null;
	const originalKeyText = getConfigValue(configEntries, "Key");
	const parsedOriginalKey = parseMainKey(originalKeyText);
	const selectedKeyText = normalizeStructureKeyOption((options.selectedStructureKeys && typeof options.selectedStructureKeys === "object" ? options.selectedStructureKeys : {})["config-structure"]) || parsedOriginalKey?.raw || originalKeyText;
	const transposition = createChordTransposition(parsedOriginalKey?.raw || "", selectedKeyText);
	const allSteps = parseStructureSteps(structureEntry);
	const partNameFilter = normalizePartNameFilter(options);
	const steps = filterStepsByPartName(allSteps, partNameFilter);
	const noteSteps = partNameFilter && steps.length ? [] : filterStepsByPartName(listUnplacedNoteSteps(partMap, allSteps, options), partNameFilter);
	const strummingPatternLines = options.hideStrummingPatterns ? [] : createPlainTextStrummingPatternLines(configEntries, { patterns: patternPreviewContext?.patterns });
	const structureLine = createPlainTextStructureLine(structureEntry, allSteps);
	const title = getPlainTextConfigValue(configEntries, "Title") || "Untitled Song";
	const secondaryText = [getPlainTextConfigValue(configEntries, "Subtitle"), getPlainTextConfigValue(configEntries, "Artist")].filter(Boolean).join(" · ");
	const metaLine = createPlainTextMetaSummaryEntries(configEntries, { keyTextOverride: selectedKeyText }).map(({ field, value }) => `${field}: ${value}`).join(", ");
	const configFieldLines = createPlainTextAdditionalConfigLines(configEntries, options);
	return {
		attachments: createOpenLyricAttachments(getConfigValueLines(configEntries, "Attachments")),
		configFieldLines,
		title,
		secondaryText,
		metaLine,
		strummingPatternLines,
		structureLine,
		sections: [...createSongSectionsPlainTextData(steps, partMap, transposition, {
			hideBracketedKeys: Boolean(options.hideBracketedKeys),
			hideLeadingBars: Boolean(options.hideLeadingBars),
			simplifyChords: Boolean(options.simplifyChords)
		}), ...createSongSectionsPlainTextData(noteSteps, partMap, transposition, {
			hideBracketedKeys: Boolean(options.hideBracketedKeys),
			hideLeadingBars: Boolean(options.hideLeadingBars),
			simplifyChords: Boolean(options.simplifyChords)
		}).map((sectionData) => ({
			...sectionData,
			isNote: true
		}))]
	};
}
function renderOpenLyricPlainText(markdown, options = {}) {
	const presentationData = createOpenLyricPresentationData(markdown, options);
	if (!presentationData) return "";
	return [normalizePartNameFilter(options) ? "" : [
		presentationData.title,
		presentationData.secondaryText,
		presentationData.metaLine,
		...Array.isArray(presentationData.strummingPatternLines) ? presentationData.strummingPatternLines : [],
		presentationData.structureLine,
		...Array.isArray(presentationData.configFieldLines) ? presentationData.configFieldLines : []
	].filter(Boolean).join("\n"), presentationData.sections.map((sectionData) => renderSongSectionPlainTextData(sectionData)).filter(Boolean).join("\n\n")].filter(Boolean).join("\n\n").trim();
}
function renderConfigStructureCollection(entryMap, partMap, options = {}) {
	const structureEntry = entryMap.get("Structure") || null;
	const parsedOriginalKey = parseMainKey(getConfigValue(entryMap, "Key"));
	const selectedStructureKeys = options.selectedStructureKeys && typeof options.selectedStructureKeys === "object" ? options.selectedStructureKeys : {};
	const structureKeyId = "config-structure";
	const selectedKeyText = normalizeStructureKeyOption(selectedStructureKeys[structureKeyId]) || parsedOriginalKey?.raw || "";
	const metaSummary = renderMetaSummary(entryMap, {
		keyTextOverride: selectedKeyText,
		labels: options.labels
	});
	const structureOverview = structureEntry ? renderReadOnlyStructureValue(structureEntry.values) : "";
	const hideBracketedKeys = Boolean(options.hideBracketedKeys);
	const simplifyChords = Boolean(options.simplifyChords);
	const sectionPreviewHelpers = createPreviewHelpers({
		hideBracketedKeys,
		hideLeadingBars: Boolean(options.hideLeadingBars),
		showComments: Boolean(options.showComments),
		patternPreviewContext: options.patternPreviewContext || null,
		patternPreviewTargetIdPrefix: OPEN_LYRIC_PATTERN_TARGET_ID_PREFIX
	});
	const transposition = createChordTransposition(parsedOriginalKey?.raw || "", selectedKeyText);
	const partNameFilter = normalizePartNameFilter(options);
	const allSteps = parseStructureSteps(structureEntry);
	const steps = filterStepsByPartName(allSteps, partNameFilter);
	const noteSteps = filterStepsByPartName(listUnplacedNoteSteps(partMap, allSteps, options), steps.length ? "" : partNameFilter);
	const shownNoteSteps = partNameFilter && steps.length ? [] : noteSteps;
	if (partNameFilter && !steps.length && !shownNoteSteps.length) return "";
	const structureBody = partNameFilter ? "" : `${metaSummary ? "<div class=\"ol-song-view__structure-meta\">" + metaSummary + "</div>" : ""}${structureOverview ? "<div class=\"ol-song-view__structure-overview\">" + structureOverview + "</div>" : ""}`;
	return [
		"<div class=\"ol-song-view__structures\">",
		[
			`<div class="ol-song-view__structure" data-structure-key-id="${previewHelpers.escapeHtml(structureKeyId)}">`,
			`<div class="ol-song-view__structure-body">${structureBody}${steps.length || !partNameFilter ? renderSongSections(steps, partMap, transposition, {
				simplifyChords,
				showComments: Boolean(options.showComments),
				previewHelpers: sectionPreviewHelpers
			}) : ""}${renderNoteSections(shownNoteSteps, partMap, transposition, {
				simplifyChords,
				showComments: Boolean(options.showComments),
				previewHelpers: sectionPreviewHelpers,
				withDivider: !partNameFilter
			})}</div>`,
			"</div>"
		].join(""),
		"</div>"
	].join("");
}
function renderOpenLyricPreviewHtml(markdown, context = {}) {
	const options = context.viewOptions && typeof context.viewOptions === "object" ? context.viewOptions : {};
	const fences = parseOpenLyricFences(markdown);
	const configFence = fences.find((fence) => fence.parsedHeader.header === "Config") || null;
	const configEntries = createConfigEntryMap(parseConfigEntries(configFence));
	const partMap = createDeclaredPartMap(fences);
	if (!configFence) return "<div class=\"ol-song-view__empty\">Add an ol:Config fence to render the Open Lyric view.</div>";
	const resolvedOptions = {
		...options,
		patternPreviewContext: options.patternPreviewContext || createStrummingPatternPreviewContextFromConfigBody(configFence.body)
	};
	const sections = renderConfigStructureCollection(configEntries, partMap, resolvedOptions);
	if (normalizePartNameFilter(resolvedOptions)) return sections ? [
		"<section class=\"ol-song-view\">",
		sections,
		"</section>"
	].join("") : "";
	return [
		"<section class=\"ol-song-view\">",
		renderConfigHeader(configEntries, resolvedOptions),
		sections,
		"</section>"
	].join("");
}
var openLyricPreviewParser = new OLParser({
	marked: renderOpenLyricPreviewHtml,
	beforeMarked: normalizeNewlines$1,
	afterMarked: renderOpenLyricInlineMarkdown
});
function renderOpenLyricPreview(markdown, options = {}) {
	return openLyricPreviewParser.parse(markdown, { context: { viewOptions: options } });
}
//#endregion
//#region src/open-lyric-mcp/operations/music.ts
/**
* Music theory over a song: transposing the notation itself (every chord
* annotation and progression token, plus the Config `Key`), single chords,
* the chords of a key, and a chord's voicings on guitar or ukulele from the
* chord database the editor's chord popup uses.
*/
var BARE_CHORD_RE = new RegExp(`^${CHORD_SYMBOL_SOURCE}$`);
var INLINE_CHORD_RE = /\[([^\[\]\r\n]+)\]/g;
var COMMENT_LINE_RE = /^\s*\/\//;
var CONFIG_KEY_LINE_RE = /^\s*-\s*Key\s*:(.*)$/;
function readSongKey(text) {
	const configFence = parseOpenLyricFences(text).find((fence) => fence.parsedHeader?.header === "Config");
	for (const line of String(configFence?.body ?? "").split("\n")) {
		const match = line.match(CONFIG_KEY_LINE_RE);
		if (match) return match[1].trim();
	}
	return "";
}
function requireKey(keyText) {
	const parsed = parseMainKey(keyText);
	if (!parsed) throw new SongOperationError(`"${keyText}" is not a key Open Lyric knows. Use one of: ${CONFIG_KEY_VALUES.join(", ")}.`);
	return parsed;
}
function resolveSongTransposition(text, { toKey, semitones }) {
	const fromKeyText = readSongKey(text);
	const fromKey = fromKeyText ? parseMainKey(fromKeyText) : null;
	if (toKey) {
		const targetKey = requireKey(toKey);
		if (!fromKey) throw new SongOperationError("The song declares no valid Config Key, so there is nothing to move from — pass semitones instead, or set Key first.");
		if (fromKey.isMinor !== targetKey.isMinor) throw new SongOperationError(`Transposing keeps the mode: ${fromKey.raw} is ${fromKey.isMinor ? "minor" : "major"}, ${targetKey.raw} is ${targetKey.isMinor ? "minor" : "major"}.`);
		const targetKeyText = getAdjacentChromaticKey(targetKey.raw, 0, CONFIG_KEY_VALUES);
		return {
			transposition: createChordTransposition(fromKey.raw, targetKeyText),
			fromKey: fromKey.raw,
			toKey: targetKeyText
		};
	}
	const steps = Number(semitones);
	if (!Number.isInteger(steps)) throw new SongOperationError("Pass either toKey or a whole number of semitones.");
	if (fromKey) {
		const targetKeyText = getAdjacentChromaticKey(fromKey.raw, steps, CONFIG_KEY_VALUES);
		return {
			transposition: createChordTransposition(fromKey.raw, targetKeyText),
			fromKey: fromKey.raw,
			toKey: targetKeyText
		};
	}
	return {
		transposition: {
			isActive: (steps % 12 + 12) % 12 !== 0,
			semitoneOffset: steps,
			targetKeyText: ""
		},
		fromKey: "",
		toKey: ""
	};
}
/**
* Transpose the `[Chord]` annotations of one lyric line — only bracketed text
* that *is* a chord symbol, so a bracketed word in a free-text section stays
* as written.
*/
function transposeInlineChords(line, transposition) {
	return line.replace(INLINE_CHORD_RE, (match, inner) => {
		const chordText = inner.trim();
		if (!BARE_CHORD_RE.test(chordText)) return match;
		return `[${transposeChordSymbol(chordText, transposition.semitoneOffset, transposition.targetKeyText)}]`;
	});
}
function transposeSong(text, options) {
	const source = String(text ?? "");
	const { transposition, fromKey, toKey } = resolveSongTransposition(source, options);
	const lines = splitLines(source);
	parseOpenLyricFences(source).forEach((fence) => {
		const kind = String(fence.parsedHeader?.kind ?? "");
		const isConfig = fence.parsedHeader?.header === "Config";
		for (let lineNumber = fence.startLineNumber + 1; lineNumber < fence.endLineNumber; lineNumber += 1) {
			const line = lines[lineNumber - 1] ?? "";
			if (isConfig) {
				if (toKey && CONFIG_KEY_LINE_RE.test(line)) lines[lineNumber - 1] = buildConfigTextFieldLine(line, "Key", toKey) ?? line;
				continue;
			}
			if (!transposition.isActive || COMMENT_LINE_RE.test(line)) continue;
			lines[lineNumber - 1] = isProgressionSectionText(line, kind) ? transposeSectionText(line, kind, transposition) : transposeInlineChords(line, transposition);
		}
	});
	const nextText = lines.join("\n");
	return {
		text: nextText,
		fromKey,
		toKey,
		semitones: transposition.semitoneOffset,
		changedLines: countChangedLines(source, nextText)
	};
}
function transposeChord(chord, { semitones, fromKey, toKey }) {
	const chordText = normalizeChordText(chord);
	if (!BARE_CHORD_RE.test(chordText)) throw new SongOperationError(`"${chord}" is not an Open Lyric chord symbol (e.g. C, Am, Bm7, Cadd9, Gsus4, D/F#).`);
	if (fromKey || toKey) {
		if (!fromKey || !toKey) throw new SongOperationError("Pass both fromKey and toKey, or semitones.");
		const transposition = createChordTransposition(requireKey(fromKey).raw, requireKey(toKey).raw);
		return {
			chord: chordText,
			transposed: transposeChordSymbol(chordText, transposition.semitoneOffset, transposition.targetKeyText),
			semitones: transposition.semitoneOffset
		};
	}
	const steps = Number(semitones);
	if (!Number.isInteger(steps)) throw new SongOperationError("Pass semitones, or fromKey and toKey.");
	return {
		chord: chordText,
		transposed: transposeChordSymbol(chordText, steps, inferChordTargetKey(chordText, steps)),
		semitones: steps
	};
}
/**
* The key a lone chord is spelled in once moved: its own root (minor for a
* minor chord) shifted by `steps` — so `D/F#` up a tone reads `E/G#`, the way
* the key of E spells it, rather than `E/Ab`.
*/
function inferChordTargetKey(chordText, steps) {
	const match = chordText.match(/^([A-G](?:#|b)?)(m(?!aj))?/);
	const key = match ? parseMainKey(`${match[1]}${match[2] ? "m" : ""}`) : null;
	return key ? getAdjacentChromaticKey(key.raw, steps, CONFIG_KEY_VALUES) : "";
}
function getKeyChords(keyText) {
	const key = requireKey(keyText);
	return {
		key: key.raw,
		tonic: String(key.tonic ?? ""),
		mode: key.isMinor ? "minor" : "major",
		diatonicTriads: getKeyDiatonicTriads(key.raw),
		keys: [...CONFIG_KEY_VALUES]
	};
}
var chordDatabases = /* @__PURE__ */ new Map();
function loadChordDatabase(instrument) {
	let database = chordDatabases.get(instrument);
	if (!database) {
		database = (instrument === "ukulele" ? import("@tombatossals/chords-db/lib/ukulele.json") : import("@tombatossals/chords-db/lib/guitar.json")).then((module) => module.default ?? module);
		chordDatabases.set(instrument, database);
	}
	return database;
}
function toVoicing(position) {
	return {
		frets: [...position.frets ?? []],
		fingers: [...position.fingers ?? []],
		baseFret: Math.max(position.baseFret ?? 1, 1),
		barres: [...position.barres ?? []],
		capo: Boolean(position.capo),
		midi: [...position.midi ?? []]
	};
}
async function describeChord(chord, { instrument = "guitar", limit = 4 } = {}) {
	const chordText = normalizeChordText(chord);
	const valid = BARE_CHORD_RE.test(chordText);
	const description = {
		chord: chordText,
		valid,
		name: describeChordKey(chordText).replace(/^Chord\s+/, ""),
		simplified: valid ? simplifyChordSymbol(chordText) : chordText,
		degreeHints: valid ? createChordDegreeHints(chordText) : [],
		instrument,
		voicings: []
	};
	const search = valid ? createChordDatabaseSearchData(chordText) : null;
	if (!search) return description;
	const entry = resolveMatchingChordEntry(await loadChordDatabase(instrument), search, { allowMajorFallback: false });
	if (!entry) return description;
	const ranked = rankChordPositions(entry.positions, search.bassPitchClass);
	const voicings = ranked.slice(0, Math.max(1, limit)).map(toVoicing);
	description.matched = {
		root: entry.key,
		suffix: entry.suffix
	};
	description.voicings = voicings;
	if (ranked.length) description.diagram = createSvguitarData(ranked[0]);
	return description;
}
//#endregion
//#region src/open-lyric-mcp/tools/music.ts
var READ_ONLY$1 = {
	readOnlyHint: true,
	openWorldHint: false
};
function registerMusicTools({ server, files }) {
	server.registerTool("transpose_song", {
		title: "Transpose a song",
		description: "Rewrite the notation in another key: every [Chord] annotation and progression chord, plus the Config Key. Give toKey (same mode as the song) or semitones. Bracketed text that is not a chord is left alone. With path, the file is rewritten unless dryRun.",
		inputSchema: {
			...editShape,
			toKey: keySchema.optional(),
			semitones: z.number().int().min(-11).max(11).optional().describe("Used when toKey is not given; negative moves down.")
		},
		outputSchema: {
			...editOutputShape,
			fromKey: z.string(),
			toKey: z.string(),
			semitones: z.number(),
			changedLines: z.number()
		},
		annotations: {
			destructiveHint: true,
			idempotentHint: false,
			openWorldHint: false
		}
	}, ({ toKey, semitones, dryRun, ...args }) => runTool(async () => {
		const source = await readSongSource(files, args);
		const result = transposeSong(source.text, {
			toKey,
			semitones
		});
		return finishSongEdit(files, source, {
			...result,
			validation: validateSong(result.text)
		}, {
			dryRun,
			summary: `Transposed ${result.fromKey || "(no key)"} → ${result.toKey || `${result.semitones} semitone(s)`}: ${result.changedLines} line(s) changed.`
		});
	}));
	server.registerTool("transpose_chord", {
		title: "Transpose a chord",
		description: "Move one chord symbol by semitones, or from one key to another (spelled the way the target key spells it).",
		inputSchema: {
			chord: z.string().describe("e.g. \"D/F#\", \"Bm7\", \"Cadd9\"."),
			semitones: z.number().int().min(-11).max(11).optional(),
			fromKey: keySchema.optional(),
			toKey: keySchema.optional()
		},
		outputSchema: {
			chord: z.string(),
			transposed: z.string(),
			semitones: z.number()
		},
		annotations: READ_ONLY$1
	}, (args) => runTool(() => {
		const result = transposeChord(args.chord, args);
		return structuredResult(result, `${result.chord} → ${result.transposed}`);
	}));
	server.registerTool("get_key_chords", {
		title: "A key's chords",
		description: "The diatonic triads of a key (I ii iii IV V vi vii° for major, i ii° III iv v VI VII for minor) and the keys Config accepts.",
		inputSchema: { key: keySchema },
		outputSchema: {
			key: z.string(),
			tonic: z.string(),
			mode: z.enum(["major", "minor"]),
			diatonicTriads: z.array(z.string()),
			keys: z.array(z.string())
		},
		annotations: READ_ONLY$1
	}, ({ key }) => runTool(() => {
		const result = getKeyChords(key);
		return structuredResult(result, `${result.key}: ${result.diatonicTriads.join(" ")}`);
	}));
	server.registerTool("describe_chord", {
		title: "Describe a chord",
		description: "Whether a chord symbol is valid Open Lyric, its name, simplified triad and degree hints, and its fingerings on guitar or ukulele (easiest first), with SVGuitar diagram data for the first.",
		inputSchema: {
			chord: z.string(),
			instrument: z.enum(["guitar", "ukulele"]).optional(),
			limit: z.number().int().min(1).max(12).optional().describe("How many voicings (default 4).")
		},
		outputSchema: {
			chord: z.string(),
			valid: z.boolean(),
			name: z.string(),
			simplified: z.string(),
			degreeHints: z.array(z.string()),
			instrument: z.enum(["guitar", "ukulele"]),
			matched: z.object({
				root: z.string(),
				suffix: z.string()
			}).optional(),
			voicings: z.array(z.object({
				frets: z.array(z.number()).describe("Per string, lowest first: -1 muted, 0 open."),
				fingers: z.array(z.number()),
				baseFret: z.number(),
				barres: z.array(z.number()),
				capo: z.boolean(),
				midi: z.array(z.number())
			})),
			diagram: z.looseObject({}).optional()
		},
		annotations: READ_ONLY$1
	}, ({ chord, instrument, limit }) => runTool(async () => {
		const result = await describeChord(chord, {
			instrument,
			limit
		});
		return structuredResult(result, result.valid ? `${result.chord} (${result.name}): ${result.voicings.length} ${result.instrument} voicing(s).` : `"${result.chord}" is not a valid Open Lyric chord symbol.`);
	}));
}
//#endregion
//#region src/open-lyric-mcp/tools/reference.ts
var READ_ONLY = {
	readOnlyHint: true,
	openWorldHint: false
};
function registerReferenceTools({ server }) {
	server.registerTool("list_examples", {
		title: "List the example songs",
		description: "The bundled example songs — each shows a different part of the notation.",
		inputSchema: {},
		outputSchema: { examples: z.array(z.object({
			id: z.string(),
			fileName: z.string(),
			title: z.string(),
			description: z.string()
		})) },
		annotations: READ_ONLY
	}, () => runTool(() => {
		const examples = listExamples();
		return structuredResult({ examples }, examples.map((example) => `${example.id}: ${example.title}`).join("\n"));
	}));
	server.registerTool("get_example", {
		title: "Get an example song",
		description: "The full notation of one bundled example (see list_examples).",
		inputSchema: { id: z.string().describe("e.g. \"example1\" or \"example1.ol.md\".") },
		outputSchema: {
			id: z.string(),
			fileName: z.string(),
			title: z.string(),
			description: z.string(),
			text: z.string()
		},
		annotations: READ_ONLY
	}, ({ id }) => runTool(() => {
		const example = getExample(id);
		return {
			content: [{
				type: "text",
				text: example.text
			}],
			structuredContent: { ...example }
		};
	}));
	server.registerTool("get_notation_reference", {
		title: "Read the notation reference",
		description: "The Open Lyric notation reference: fences, sections, inline notation (chords, bars, repeats, directives), Config, Structure, every diagnostic, a complete example, and the machine-readable schemas. Without section: the list of sections. Read it before writing a song by hand.",
		inputSchema: { section: z.string().optional().describe("A section number (\"3\") or title (\"Structure\").") },
		outputSchema: {
			sections: z.array(z.object({
				id: z.string(),
				title: z.string()
			})),
			section: z.object({
				id: z.string(),
				title: z.string(),
				text: z.string()
			}).optional()
		},
		annotations: READ_ONLY
	}, ({ section }) => runTool(() => {
		const sections = listNotationSections().map(({ id, title }) => ({
			id,
			title
		}));
		if (!section) return structuredResult({ sections }, sections.map((entry) => `${entry.id}. ${entry.title}`).join("\n"));
		const found = getNotationSection(section);
		return {
			content: [{
				type: "text",
				text: found.text
			}],
			structuredContent: {
				sections,
				section: found
			}
		};
	}));
	server.registerTool("list_fence_types", {
		title: "List the section types",
		description: "Every ol: fence type: header, kind, whether it is numbered, its Structure code, and its body rule (lyric, progression, mixed, freeText).",
		inputSchema: {},
		outputSchema: {
			fences: z.array(z.object({
				header: z.string(),
				kind: z.string(),
				description: z.string(),
				numbered: z.boolean(),
				required: z.boolean(),
				allowsDuplicates: z.boolean(),
				structureCode: z.string().nullable(),
				bodyRule: z.string(),
				bodyRuleDescription: z.string(),
				example: z.string()
			})),
			structureCodes: z.array(z.object({
				code: z.string(),
				header: z.string(),
				numbered: z.boolean()
			}))
		},
		annotations: READ_ONLY
	}, () => runTool(() => {
		const fences = listFenceTypes();
		return structuredResult({
			fences,
			structureCodes: listStructureCodes()
		}, fences.map((fence) => `${fence.header}${fence.structureCode ? ` (${fence.structureCode})` : ""}: ${fence.bodyRule}`).join("\n"));
	}));
	server.registerTool("get_config_fields", {
		title: "List the Config fields",
		description: "Every ol:Config field: required or not, multiline or not, aliases, and its closed value set (Key, Time, Locales) or pattern (Tempo).",
		inputSchema: {},
		outputSchema: { fields: z.array(z.object({
			name: z.string(),
			required: z.boolean(),
			multiline: z.boolean(),
			aliases: z.array(z.string()),
			values: z.array(z.string()).optional(),
			pattern: z.string().optional(),
			note: z.string()
		})) },
		annotations: READ_ONLY
	}, () => runTool(() => {
		const fields = listConfigFields();
		return structuredResult({ fields }, fields.map((field) => `${field.name}${field.required ? " (required)" : ""}: ${field.note}`).join("\n"));
	}));
}
//#endregion
//#region src/open-lyric-mcp/document-theme.scss?inline
var document_theme_default = ":root{--page-background:radial-gradient(circle at 0% 0%, #fffdf5, #f4f3ee 45%, #ece9dd 100%);--surface:#fff;--surface-elevated:#fff;--ink:#1f2a37;--muted:#495057;--line:#d8d5c8;--heading:#213547;--accent:#115e59;--accent-halo:#115e5933;--focus-ring-rgb:17, 94, 89;--shell-resize-hide:#dc2626;--shell-resize-hide-halo:#dc26262e;--unsaved:#dc2626;--unsaved-halo:#dc26262e;--shadow:0 12px 28px #1f2a3714;--drop-text:#0f4c47;--drop-scrim:#ffffffc2;--preview-code-bg:#f6f8fa;--preview-code-border:#e1e4e8;--theme-toggle-border:#9ca3af;--theme-toggle-hover-bg:#ecfdf5;--toolbar-icon-active-bg:#115e591f;--toolbar-icon-active-border:#115e5970;--toolbar-icon-active-ink:#0f4c47;--settings-menu-shadow:var(--shadow);--floating-trigger-shadow:0 .18rem .45rem #0f172a14, 0 .7rem 1.6rem #0f172a29;color-scheme:light}:root[data-theme=dark]{--page-background:radial-gradient(circle at 0% 0%, #13222a, #0e1720 45%, #080d13 100%);--surface:#101923;--surface-elevated:#101923d1;--ink:#e5edf5;--muted:#94a3b8;--line:#223242;--heading:#f8fafc;--accent:#4fd1c5;--accent-halo:#4fd1c540;--focus-ring-rgb:79, 209, 197;--shell-resize-hide:#f87171;--shell-resize-hide-halo:#f871713d;--unsaved:#f87171;--unsaved-halo:#f871713d;--shadow:0 16px 34px #00000057;--drop-text:#d8fbf6;--drop-scrim:#080d13d1;--preview-code-bg:#18232f;--preview-code-border:#2b3e50;--theme-toggle-border:#5f7388;--theme-toggle-hover-bg:#18303b;--toolbar-icon-active-bg:#4fd1c529;--toolbar-icon-active-border:#4fd1c57a;--toolbar-icon-active-ink:#d8fbf6;--settings-menu-shadow:0 .2rem .55rem #00000038, 0 .85rem 1.9rem #00000061;--floating-trigger-shadow:0 .2rem .55rem #00000038, 0 .85rem 1.9rem #00000061;color-scheme:dark}body{background:var(--surface);color:var(--ink);margin:0;font-family:system-ui,-apple-system,Segoe UI,Roboto,Noto Sans,Noto Sans Khmer,sans-serif}.ol-mcp-document{box-sizing:border-box;max-width:960px;margin:0 auto}@media print{.ol-mcp-document{max-width:none}}";
//#endregion
//#region src/plugins/OpenLyric/preview/styles.scss?inline
var styles_default = ":root{--preview-ol-border:#cfe2dd;--preview-ol-border-current:var(--preview-ol-border);--preview-ol-heading:#163b39;--preview-ol-muted:#68804b;--preview-ol-chip-bg:#115e5914;--preview-ol-chip-border:#115e5933;--preview-ol-token:#8c5a13;--preview-ol-accent-current:var(--accent);--preview-repeat-bg:#ffffff34;--preview-repeat-border:#dc2626;--preview-repeat-text:black;--song-view-chord:#ef4444;--song-view-muted:#6b7280;--song-view-pattern-card-bg:#ffffffd1;--song-view-pattern-bg:linear-gradient(180deg, #fffffffa 0%, #f8fafcf5 100%);--song-view-pattern-border:#0f172a14;--song-view-pattern-ink:#111827;--song-view-pattern-divider:#64748b47;--chord-popup-bg:linear-gradient(180deg, #fffffffa 0%, #f4f7f5fa 100%);--chord-popup-border:#115e5933;--chord-popup-shadow:0 22px 44px #1f2a372e;--chord-popup-diagram-bg:linear-gradient(180deg, #fffffffa 0%, #f7fafcfa 100%);--chord-popup-diagram-surface:#fff;--chord-popup-diagram-border:#115e5929;--chord-popup-diagram-ink:#102a43;--chord-popup-diagram-line:#1f2a3757;--chord-popup-diagram-label:#52606d;--chord-popup-diagram-shadow:inset 0 1px 0 #ffffffc7;--preview-ol-bg:transparent}:root[data-theme=dark],[data-ol-theme=dark]{--preview-ol-bg:linear-gradient(180deg, #13222a 0%, #111b24 100%);--preview-ol-border:#28404e;--preview-ol-border-current:var(--preview-ol-border);--preview-ol-heading:#ecfeff;--preview-ol-muted:#a2c875;--preview-ol-chip-bg:#4fd1c51a;--preview-ol-chip-border:#4fd1c53d;--preview-ol-token:#ffd089;--preview-ol-accent-current:var(--accent);--preview-repeat-bg:#00000034;--preview-repeat-border:#f87171;--preview-repeat-text:white;--song-view-chord:#f87171;--song-view-muted:#94a3b8;--song-view-pattern-card-bg:#0c141ce0;--song-view-pattern-bg:linear-gradient(180deg, #13222af5 0%, #0b141df0 100%);--song-view-pattern-border:#94a3b838;--song-view-pattern-ink:#f8fafc;--song-view-pattern-divider:#94a3b847;--chord-popup-bg:linear-gradient(180deg, #13222afa 0%, #0b141dfa 100%);--chord-popup-border:#4fd1c538;--chord-popup-shadow:0 22px 46px #0000006b;--chord-popup-diagram-bg:linear-gradient(180deg, #080d13fa 0%, #0f1720fa 100%);--chord-popup-diagram-surface:#0c1720;--chord-popup-diagram-border:#4fd1c52e;--chord-popup-diagram-ink:#f8fafc;--chord-popup-diagram-line:#e5edf566;--chord-popup-diagram-label:#cbd5e1;--chord-popup-diagram-shadow:inset 0 1px 0 #ffffff0a}:root[data-theme=light-bs],[data-ol-theme=light-bs]{--preview-ol-border:#dee2e6;--preview-ol-border-current:var(--preview-ol-border);--preview-ol-heading:#000;--preview-ol-muted:#6c757d;--preview-ol-chip-bg:#0d6efd1a;--preview-ol-chip-border:#0d6efd40;--preview-ol-token:#997404;--preview-ol-accent-current:var(--accent);--preview-repeat-bg:#fff3;--preview-repeat-border:#dc3545;--preview-repeat-text:#212529;--song-view-chord:#d63384;--song-view-muted:#6c757d;--song-view-pattern-card-bg:#fff;--song-view-pattern-bg:#f8f9fa;--song-view-pattern-border:#dee2e6;--song-view-pattern-ink:#212529;--song-view-pattern-divider:#2125292d;--chord-popup-bg:#fff;--chord-popup-border:#dee2e6;--chord-popup-shadow:0 1rem 3rem #0000002d;--chord-popup-diagram-bg:#f8f9fa;--chord-popup-diagram-surface:#fff;--chord-popup-diagram-border:#dee2e6;--chord-popup-diagram-ink:#212529;--chord-popup-diagram-line:#21252980;--chord-popup-diagram-label:#6c757d;--chord-popup-diagram-shadow:none;--preview-ol-bg:transparent}:root[data-theme=dark-bs],[data-ol-theme=dark-bs]{--preview-ol-bg:#2b3035;--preview-ol-border:#495057;--preview-ol-border-current:var(--preview-ol-border);--preview-ol-heading:#fff;--preview-ol-muted:#adb5bd;--preview-ol-chip-bg:#6ea8fe24;--preview-ol-chip-border:#6ea8fe52;--preview-ol-token:#ffda6a;--preview-ol-accent-current:var(--accent);--preview-repeat-bg:#0003;--preview-repeat-border:#ea868f;--preview-repeat-text:#dee2e6;--song-view-chord:#e685b5;--song-view-muted:#adb5bd;--song-view-pattern-card-bg:#343a40;--song-view-pattern-bg:#2b3035;--song-view-pattern-border:#495057;--song-view-pattern-ink:#fff;--song-view-pattern-divider:#dee2e640;--chord-popup-bg:#2b3035;--chord-popup-border:#495057;--chord-popup-shadow:0 1rem 3rem #0009;--chord-popup-diagram-bg:#212529;--chord-popup-diagram-surface:#2b3035;--chord-popup-diagram-border:#495057;--chord-popup-diagram-ink:#fff;--chord-popup-diagram-line:#dee2e680;--chord-popup-diagram-label:#adb5bd;--chord-popup-diagram-shadow:none}[data-ol-theme=light]{--preview-ol-border:#cfe2dd;--preview-ol-border-current:var(--preview-ol-border);--preview-ol-heading:#163b39;--preview-ol-muted:#68804b;--preview-ol-chip-bg:#115e5914;--preview-ol-chip-border:#115e5933;--preview-ol-token:#8c5a13;--preview-ol-accent-current:var(--accent);--preview-repeat-bg:#ffffff34;--preview-repeat-border:#dc2626;--preview-repeat-text:black;--song-view-chord:#ef4444;--song-view-muted:#6b7280;--song-view-pattern-card-bg:#ffffffd1;--song-view-pattern-bg:linear-gradient(180deg, #fffffffa 0%, #f8fafcf5 100%);--song-view-pattern-border:#0f172a14;--song-view-pattern-ink:#111827;--song-view-pattern-divider:#64748b47;--chord-popup-bg:linear-gradient(180deg, #fffffffa 0%, #f4f7f5fa 100%);--chord-popup-border:#115e5933;--chord-popup-shadow:0 22px 44px #1f2a372e;--chord-popup-diagram-bg:linear-gradient(180deg, #fffffffa 0%, #f7fafcfa 100%);--chord-popup-diagram-surface:#fff;--chord-popup-diagram-border:#115e5929;--chord-popup-diagram-ink:#102a43;--chord-popup-diagram-line:#1f2a3757;--chord-popup-diagram-label:#52606d;--chord-popup-diagram-shadow:inset 0 1px 0 #ffffffc7;--preview-ol-bg:transparent}.ol-lyric-panel .topbar-settings__open-lyric-controls,.ol-standalone-preview .topbar-settings__open-lyric-controls{gap:.5rem;display:grid}.ol-lyric-panel .topbar-settings__open-lyric-row,.ol-standalone-preview .topbar-settings__open-lyric-row{flex-wrap:wrap;align-items:center;gap:.45rem;display:flex}.ol-lyric-panel .topbar-settings__open-lyric-row--wrap,.ol-standalone-preview .topbar-settings__open-lyric-row--wrap{gap:.35rem}.ol-lyric-panel .topbar-settings__open-lyric-toggle-group,.ol-standalone-preview .topbar-settings__open-lyric-toggle-group{width:100%;max-width:100%}.ol-lyric-panel .topbar-settings__open-lyric-toggle-group>.topbar-settings__open-lyric-toggle-btn,.ol-standalone-preview .topbar-settings__open-lyric-toggle-group>.topbar-settings__open-lyric-toggle-btn{--bs-btn-color:var(--heading);--bs-btn-bg:transparent;--bs-btn-border-color:var(--preview-ol-border-current);--bs-btn-hover-color:var(--preview-ol-accent-current);--bs-btn-hover-bg:color-mix(in srgb, var(--preview-ol-accent-current) 10%, transparent);--bs-btn-hover-border-color:var(--preview-ol-accent-current);--bs-btn-active-color:var(--preview-ol-accent-current);--bs-btn-active-bg:color-mix(in srgb, var(--preview-ol-accent-current) 16%, transparent);--bs-btn-active-border-color:var(--preview-ol-accent-current);--bs-btn-focus-shadow-rgb:var(--focus-ring-rgb);white-space:nowrap;flex:1 1 0;min-width:0;font-size:.78rem;font-weight:600;line-height:1.15}.ol-lyric-panel .topbar-settings__open-lyric-toggle-group>.topbar-settings__open-lyric-toggle-btn[aria-pressed=true],.ol-standalone-preview .topbar-settings__open-lyric-toggle-group>.topbar-settings__open-lyric-toggle-btn[aria-pressed=true]{--bs-btn-color:var(--preview-ol-accent-current);--bs-btn-bg:color-mix(in srgb, var(--preview-ol-accent-current) 18%, transparent);--bs-btn-border-color:var(--preview-ol-accent-current);--bs-btn-hover-color:var(--preview-ol-accent-current);--bs-btn-hover-bg:color-mix(in srgb, var(--preview-ol-accent-current) 22%, transparent);--bs-btn-hover-border-color:var(--preview-ol-accent-current)}.ol-lyric-panel .topbar-settings__structure-label,.ol-standalone-preview .topbar-settings__structure-label{color:var(--muted);font-size:.78rem;font-weight:600}.ol-lyric-panel .topbar-settings__structure-key-control,.ol-standalone-preview .topbar-settings__structure-key-control{flex-wrap:wrap}.ol-lyric-panel [data-ol-ref=openLyricPreview]{height:auto;min-height:0;color:var(--ink);overscroll-behavior:contain;line-height:1.6;font-family:var(--ol-font-family,inherit);font-size:var(--ol-font-size,inherit);flex:auto;padding:1.25rem;overflow:auto}.ol-lyric-panel [data-ol-ref=openLyricPreview]>:first-child{margin-top:0}.ol-lyric-panel [data-ol-ref=openLyricPreview]>:last-child{margin-bottom:0}.ol-lyric-panel [data-ol-ref=openLyricPreview]>*{box-sizing:border-box;width:fit-content}.ol-lyric-panel [data-ol-ref=openLyricPreview] a{color:var(--accent)}.ol-lyric-panel [data-ol-ref=openLyricPreview] h1,.ol-lyric-panel [data-ol-ref=openLyricPreview] h2,.ol-lyric-panel [data-ol-ref=openLyricPreview] h3{color:var(--heading);margin-top:.25rem}.ol-lyric-panel [data-ol-ref=openLyricPreview] pre{background:var(--preview-code-bg);border:1px solid var(--preview-code-border);border-radius:.5rem;padding:.75rem;overflow:auto}.open-lyric-render-surface{height:auto;max-height:none;color:var(--ink);padding:1.25rem;line-height:1.6;overflow:visible}.open-lyric-render-surface>:first-child{margin-top:0}.open-lyric-render-surface>:last-child{margin-bottom:0}.open-lyric-render-surface a,:where(.ol-preview-root) a{color:var(--accent)}.open-lyric-render-surface h1,.open-lyric-render-surface h2,.open-lyric-render-surface h3{color:var(--heading);margin-top:.25rem}.open-lyric-render-surface pre{background:var(--preview-code-bg);border:1px solid var(--preview-code-border);border-radius:.5rem;padding:.75rem;overflow:auto}.ol-song-view{gap:1.15rem;width:100%;display:grid}.ol-song-view__header{gap:.85rem;padding-bottom:.25rem;display:grid}.ol-song-view__headline{gap:.2rem;display:grid}.ol-song-view__header-meta{grid-template-columns:repeat(auto-fit,minmax(min(100%,17rem),1fr));align-items:start;gap:.65rem 1.75rem;display:grid}.ol-song-view__header-group{align-content:start;gap:.6rem;min-width:0;display:grid}.ol-song-view__title{margin:0;line-height:1.15}.ol-song-view__subtitle{color:var(--song-view-muted);margin:0;font-size:.98em}.ol-song-view__meta-line{color:var(--heading);flex-wrap:wrap;align-items:center;gap:.45em;font-size:1em;font-weight:400;display:flex}.ol-song-view__meta-entry strong{font-weight:500}.ol-song-view__meta-chord{font-size:1em;line-height:inherit;vertical-align:baseline}.ol-song-view__meta-separator{color:var(--song-view-muted)}.ol-song-view__description,.ol-song-view__copyright{margin:0}.ol-song-view__description{color:var(--ink)}.ol-song-view__copyright{color:var(--song-view-muted);font-size:.88em}.ol-song-view__details{gap:.25rem;display:grid}.ol-song-view__detail{color:var(--heading);flex-wrap:wrap;align-items:baseline;gap:.4em;font-size:.92em;display:flex}.ol-song-view__detail-label{color:var(--song-view-muted);font-weight:500}.ol-song-view__extras{gap:.3rem;min-width:0;display:grid}.ol-song-view__extras-summary{color:var(--song-view-muted);cursor:pointer;user-select:none;border-radius:.4rem;align-items:center;gap:.35rem;padding:.1rem .2rem;font-size:.92em;font-weight:500;list-style:none;display:flex}.ol-song-view__extras-summary::-webkit-details-marker{display:none}.ol-song-view__extras-summary:focus-visible{box-shadow:0 0 0 3px var(--accent-halo);outline:none}.ol-song-view__extras-items{flex-wrap:wrap;align-items:center;gap:.15rem .4rem;min-width:0;display:inline-flex}.ol-song-view__extras-separator{opacity:.6}.ol-song-view__extras-count{font-variant-numeric:tabular-nums}.ol-song-view__extras-summary:after{content:\"\";opacity:.7;border-bottom:.1rem solid;border-right:.1rem solid;flex:none;width:.42rem;height:.42rem;transition:transform .18s,opacity .18s;transform:translateY(-.1em)rotate(45deg)}.ol-song-view__extras-summary:hover:after{opacity:1}.ol-song-view__extras:not([open])>.ol-song-view__extras-summary:after{transform:translateY(-.02em)rotate(-45deg)}.ol-song-view__extras-body{gap:.25rem;min-width:0;display:grid}.ol-song-view__attachments{gap:.2rem;font-size:.92em;display:grid}.ol-song-view__attachment-list{gap:.2rem;margin:0;padding-left:1.15rem;display:grid}.ol-song-view__attachment{color:var(--ink);word-break:break-word}.ol-song-view__pattern-grid{flex-wrap:wrap;gap:.25rem;display:flex}.ol-song-view__pattern-card{border:1px solid var(--preview-ol-border);background:var(--song-view-pattern-card-bg);border-radius:.72rem;scroll-margin-top:.85rem;transition:box-shadow .18s,border-color .18s;overflow:hidden}.ol-song-view__pattern-header{flex-wrap:wrap;justify-content:space-between;align-items:flex-start;gap:.35rem .6rem;padding:.1rem;display:flex}.ol-song-view__pattern-heading{flex:auto;align-items:flex-start;gap:.12rem;min-width:0;display:flex}.ol-song-view__pattern-title{color:var(--song-view-muted);cursor:help;flex-wrap:wrap;align-items:baseline;gap:.28rem;margin:0;font-size:.72rem;display:inline-flex}.ol-song-view__pattern-index{letter-spacing:.04em;font-style:normal;font-weight:700}.ol-song-view__pattern-label{font-style:italic}.ol-song-view__pattern-display{border:1px solid var(--song-view-pattern-border);background:var(--song-view-pattern-bg);padding:.05rem .02rem .28rem;overflow:auto hidden}.ol-song-view__pattern-row{grid-template-columns:repeat(var(--pattern-column-count), minmax(.89rem, 1fr));align-items:center;display:grid}.ol-song-view__pattern-row--guide{border-bottom:1px solid var(--song-view-pattern-border);margin-bottom:.1rem;padding-bottom:.12rem}.ol-song-view__pattern-guide-cell{letter-spacing:.08em;min-height:.92rem;color:var(--song-view-muted);justify-content:center;align-items:center;font-size:.64rem;font-weight:700;display:inline-flex}.ol-song-view__pattern-guide-cell--break{border-left:1px solid var(--song-view-pattern-divider)}.ol-song-view__pattern-cell{min-height:1.25rem;color:var(--song-view-pattern-ink);user-select:none;justify-content:center;align-items:center;font-size:.8rem;line-height:1;display:inline-flex;position:relative}.ol-song-view__pattern-cell-button{appearance:none;width:100%;color:inherit;font:inherit;cursor:pointer;background:0 0;border:none;padding:0}.ol-song-view__pattern-cell-button:hover{text-shadow:0 0 4px var(--accent)}.ol-song-view__pattern-cell-button:focus-visible{box-shadow:inset 0 0 0 2px var(--accent-halo);outline:none}.ol-song-view__pattern-cell--accent{color:var(--song-view-chord);font-size:.75rem;font-weight:700}.ol-song-view__pattern-cell--stroke{min-height:.6rem;font-size:1.1rem}.ol-song-view__pattern-cell--down,.ol-song-view__pattern-cell--up{color:var(--song-view-pattern-ink)}.ol-song-view__pattern-cell--rest{color:#0000}.ol-song-view__pattern-cell--break{border-left:1px solid var(--song-view-pattern-divider)}.ol-song-view__structures{flex-wrap:wrap;align-items:flex-start;gap:.65rem;display:flex}.ol-song-view__structure{border:1px solid var(--preview-ol-border-current);background:var(--surface-elevated,var(--surface));border-radius:.85rem;width:100%;overflow:hidden}.ol-song-view__structure-actions{flex-wrap:wrap;flex:0 auto;justify-content:flex-end;align-items:center;gap:.35rem;min-width:0;max-width:100%;margin-left:auto;display:flex}.ol-song-view__structure-key-control{color:var(--song-view-muted);align-items:center;gap:.25rem;display:inline-flex}.ol-song-view__structure-key-step,.ol-song-view__structure-key-select{border:1px solid var(--preview-ol-border-current);background:var(--surface);color:var(--heading);font:inherit;font-weight:700}.ol-song-view__structure-key-step{cursor:pointer;border-radius:999px;justify-content:center;align-items:center;width:2rem;height:2rem;padding:0;display:inline-flex}.ol-song-view__structure-key-select{cursor:pointer;border-radius:999px;padding:0 .35rem;font-size:.88rem}.ol-song-view__structure-key-step:hover,.ol-song-view__structure-key-select:hover{border-color:var(--preview-ol-accent-current)}.ol-song-view__structure-key-step:focus-visible,.ol-song-view__structure-key-select:focus-visible{box-shadow:0 0 0 3px var(--accent-halo);outline:none}.ol-song-view__simplify-toggle{border:1px solid var(--preview-ol-border-current);background:var(--surface);min-height:1.85rem;color:var(--heading);font:inherit;cursor:pointer;border-radius:999px;align-items:center;gap:.35rem;padding:0 .6rem;font-size:.82rem;font-weight:600;display:inline-flex}.ol-song-view__simplify-toggle:hover{border-color:var(--preview-ol-accent-current)}.ol-song-view__simplify-toggle:focus-visible{box-shadow:0 0 0 3px var(--accent-halo);outline:none}.ol-song-view__simplify-toggle-indicator{border:1px solid var(--preview-ol-border-current);background:0 0;border-radius:.25rem;flex:none;justify-content:center;align-items:center;width:.9rem;height:.9rem;display:inline-flex}.ol-song-view__simplify-toggle[aria-pressed=true]{border-color:var(--preview-ol-accent-current);color:var(--preview-ol-accent-current)}.ol-song-view__simplify-toggle[aria-pressed=true] .ol-song-view__simplify-toggle-indicator{border-color:var(--preview-ol-accent-current);background:color-mix(in srgb, var(--preview-ol-accent-current) 18%, transparent)}.ol-song-view__simplify-toggle[aria-pressed=true] .ol-song-view__simplify-toggle-indicator:before{content:\"✓\";color:var(--preview-ol-accent-current);font-size:.72rem;line-height:1}.ol-song-view__structure-body{border-top:1px solid var(--preview-ol-border-current);padding:.35rem .4rem .5rem}.ol-song-view__structure-meta,.ol-song-view__structure-overview{border-bottom:1px solid var(--preview-ol-border-current);margin-bottom:.45rem;padding-bottom:.45rem}.ol-song-view__structure-overview .ol-preview-structure-line,.ol-song-view__structure-overview .ol-preview-structure-link{gap:.35em}.ol-song-view__structure-overview .ol-preview-structure-step{padding:.02em .35em;font-size:.88em}.ol-song-view__sections{--ol-section-column:16rem;grid-template-columns:repeat(auto-fit, minmax(min(100%, var(--ol-section-column)), 1fr));align-items:stretch;gap:.9rem .4rem;margin-top:.5rem;display:grid}.ol-song-view__notes-divider{color:var(--song-view-muted);align-items:center;gap:.6em;margin-top:1.1rem;font-size:.8em;font-weight:600;display:flex}.ol-song-view__notes-divider:before,.ol-song-view__notes-divider:after{content:\"\";border-top:1px dashed var(--preview-ol-border-current);flex:1 1 0}.ol-song-view__notes-divider-label{white-space:nowrap;flex:none}.ol-song-view__notes{margin-top:.6rem}.ol-song-view__section,.ol-song-view__info-card{min-width:0;box-shadow:1px 1px 2px color-mix(in srgb, var(--preview-ol-border-current) 20%, transparent);border-radius:.85rem;padding:.35rem}.ol-song-view__info-card{box-sizing:border-box;text-align:center;flex-direction:column;justify-content:safe center;align-items:center;gap:.85rem;height:100%;display:flex}.ol-song-view__info-card .ol-song-view__header,.ol-song-view__info-card .ol-song-view__headline,.ol-song-view__info-card .ol-song-view__header-meta,.ol-song-view__info-card .ol-song-view__header-group,.ol-song-view__info-card .ol-song-view__extras,.ol-song-view__info-card .ol-song-view__extras-body,.ol-song-view__info-card .ol-song-view__attachments{justify-items:center;width:100%}.ol-song-view__info-card .ol-song-view__header{padding-bottom:0}.ol-song-view__info-card .ol-song-view__meta-line,.ol-song-view__info-card .ol-song-view__detail,.ol-song-view__info-card .ol-song-view__pattern-grid{justify-content:center}.ol-song-view__info-card .ol-song-view__copyright,.ol-song-view__info-card .ol-song-view__meta-line{color:var(--song-view-muted);font-size:.98em;font-weight:400}.ol-song-view__info-card .ol-song-view__attachment-list{padding-left:0;list-style-position:inside}.ol-song-view__info-card .ol-song-view__structure-meta{border-bottom:0;margin-bottom:0;padding-bottom:0}.ol-song-view__section--missing{gap:.55rem}.ol-song-view__section{position:relative}.ol-song-view__section-index{background:color-mix(in srgb, var(--preview-ol-border-current) 5%, transparent);min-width:1.5em;color:var(--song-view-muted);font-variant-numeric:tabular-nums;text-align:center;user-select:none;border-radius:0 0 .75em;padding:0 .35em;font-size:.58em;line-height:1.6;position:absolute;bottom:0;right:0}.ol-song-view__section-line{flex-wrap:wrap;align-items:baseline;gap:.35rem;display:flex}.ol-song-view__section-title{text-decoration-line:underline;text-decoration-color:var(--preview-ol-border-current);text-underline-offset:.22em;margin:0 0 .95em;font-size:.8em;font-weight:500;text-decoration-thickness:.06em}.ol-lyric-panel [data-ol-ref=openLyricPreview] .ol-song-view__section-title,.open-lyric-render-surface .ol-song-view__section-title{margin-top:0}.ol-song-view__section-body{min-width:0}.ol-song-view__section-inline-body{flex:16rem;min-width:0}.ol-song-view__section-inline-body .ol-preview-line{margin-left:0}.ol-song-view .ol-preview-lines{font-variant-ligatures:none;tab-size:4}.ol-song-view__section-inline-body--text .ol-preview-lines{display:block}.ol-song-view__repeat{margin-left:0}.ol-song-view__missing-note,.ol-song-view__empty{border:1px dashed var(--preview-ol-border);color:var(--preview-ol-muted);border-radius:.9rem;padding:1rem 1.1rem}.ol-preview-fence{border:1px solid var(--preview-ol-border-current);background:var(--preview-ol-bg);border-radius:.9rem;margin:1.1rem 0;scroll-margin-top:.85rem;transition:box-shadow .18s,border-color .18s;overflow:hidden;box-shadow:0 10px 24px #10192314}.ol-preview-fence--jump-target{box-shadow:0 0 0 3px var(--accent-halo), 0 10px 24px #1019231f}.ol-preview-fence__summary{cursor:pointer;user-select:none;background:#ffffff24;align-items:center;gap:.7rem;padding:.1rem 1rem;list-style:none;display:flex}.ol-preview-fence__summary::-webkit-details-marker{display:none}.ol-preview-fence__summary:before{content:\"\";width:.6rem;height:.6rem;color:var(--preview-ol-heading);opacity:.7;border-bottom:.12rem solid;border-right:.12rem solid;flex:none;transition:transform .18s,opacity .18s;transform:translateY(-.08rem)rotate(45deg)}.ol-preview-fence:not([open]) .ol-preview-fence__summary:before{transform:translateY(-.02rem)rotate(-45deg)}.ol-preview-fence[open] .ol-preview-fence__summary{border-bottom:1px solid var(--preview-ol-border-current)}.ol-preview-fence__summary:hover:before,.ol-preview-fence__summary:focus-visible:before{opacity:1}.ol-preview-fence__summary:focus-visible{box-shadow:inset 0 0 0 2px var(--accent-halo);outline:none}.ol-preview-fence__title{color:var(--preview-ol-heading);font-size:1.05em}.ol-preview-fence__body{padding:.5rem .5rem .7rem}.ol-preview-fence__edit{appearance:none;width:1.7rem;height:1.7rem;color:var(--preview-ol-heading);cursor:pointer;opacity:.55;background:0 0;border:1px solid #0000;border-radius:.5rem;flex:none;justify-content:center;align-items:center;margin-left:auto;padding:0;transition:opacity .16s,background-color .16s,border-color .16s,color .16s;display:none}.ol-preview-fence__edit svg{width:.95rem;height:.95rem}[data-ol-section-editing=enabled] .ol-preview-fence__edit{display:inline-flex}.open-lyric-render-surface .ol-preview-fence__edit{display:none!important}.ol-preview-fence__summary:hover .ol-preview-fence__edit,.ol-preview-fence__edit:hover,.ol-preview-fence__edit:focus-visible,.ol-preview-fence[data-ol-section-editor-open=true] .ol-preview-fence__edit{opacity:1}.ol-preview-fence__edit:hover,.ol-preview-fence[data-ol-section-editor-open=true] .ol-preview-fence__edit{border-color:var(--preview-ol-border-current);background:var(--preview-ol-bg);color:var(--preview-ol-accent-current)}.ol-preview-fence__edit:focus-visible{box-shadow:0 0 0 3px var(--accent-halo);outline:none}.ol-preview-fence__rename{appearance:none;width:1.5rem;height:1.5rem;color:var(--preview-ol-heading);cursor:pointer;opacity:.45;background:0 0;border:1px solid #0000;border-radius:.5rem;flex:none;justify-content:center;align-items:center;padding:0;transition:opacity .16s,background-color .16s,border-color .16s,color .16s;display:none}.ol-preview-fence__rename svg{width:.85rem;height:.85rem}[data-ol-section-editing=enabled] .ol-preview-fence__rename{display:inline-flex}.open-lyric-render-surface .ol-preview-fence__rename{display:none!important}.ol-preview-fence__summary:hover .ol-preview-fence__rename,.ol-preview-fence__rename:hover,.ol-preview-fence__rename:focus-visible,.ol-preview-fence[data-ol-section-rename-open=true] .ol-preview-fence__rename{opacity:1}.ol-preview-fence__rename:hover,.ol-preview-fence[data-ol-section-rename-open=true] .ol-preview-fence__rename{border-color:var(--preview-ol-border-current);background:var(--preview-ol-bg);color:var(--preview-ol-accent-current)}.ol-preview-fence__rename:focus-visible{box-shadow:0 0 0 3px var(--accent-halo);outline:none}.ol-preview-fence__delete{appearance:none;width:1.7rem;height:1.7rem;color:var(--preview-ol-heading);cursor:pointer;opacity:.45;background:0 0;border:1px solid #0000;border-radius:.5rem;flex:none;justify-content:center;align-items:center;padding:0;transition:opacity .16s,background-color .16s,border-color .16s,color .16s;display:none}.ol-preview-fence__delete svg{width:.9rem;height:.9rem}[data-ol-section-editing=enabled] .ol-preview-fence__delete{display:inline-flex}.open-lyric-render-surface .ol-preview-fence__delete{display:none!important}.ol-preview-fence__summary:hover .ol-preview-fence__delete,.ol-preview-fence__delete:hover,.ol-preview-fence__delete:focus-visible,.ol-preview-fence__delete[aria-expanded=true]{opacity:1}.ol-preview-fence__delete:hover,.ol-preview-fence__delete[aria-expanded=true]{background:var(--preview-ol-bg);color:#e05260;border-color:#e05260}.ol-preview-fence__delete:focus-visible{box-shadow:0 0 0 3px var(--accent-halo);outline:none}.ol-preview-delete-section-popup{gap:.45rem;width:min(20rem,100vw - 1.5rem);padding:.75rem}.ol-preview-delete-section__question{color:var(--heading);margin:0;font-weight:600}.ol-preview-delete-section__detail{color:var(--song-view-muted);margin:0;font-size:.85em}.ol-preview-delete-section__actions{justify-content:flex-end;gap:.4rem;margin-top:.15rem;display:flex}.ol-preview-delete-section__confirm,.ol-preview-delete-section__cancel{appearance:none;border:1px solid var(--preview-ol-chip-border);background:var(--surface);color:inherit;font:inherit;cursor:pointer;border-radius:999px;padding:.4rem .9rem;transition:border-color .16s,color .16s,box-shadow .16s,transform .16s}.ol-preview-delete-section__confirm{color:#e05260;border-color:#e05260;font-weight:600}.ol-preview-delete-section__confirm:hover,.ol-preview-delete-section__confirm:focus-visible,.ol-preview-delete-section__cancel:hover,.ol-preview-delete-section__cancel:focus-visible{box-shadow:0 0 0 3px var(--accent-halo);outline:none}.ol-preview-delete-section__cancel:hover,.ol-preview-delete-section__cancel:focus-visible{border-color:var(--preview-ol-accent-current)}.ol-preview-delete-section__confirm:active,.ol-preview-delete-section__cancel:active{transform:scale(.98)}.ol-preview-fence__rename-editor{gap:.6rem;padding:.65rem .7rem .2rem;display:grid}.ol-preview-section-name{flex-wrap:wrap;align-items:flex-end;gap:.5rem .7rem;display:flex}.ol-preview-section-name__field{gap:.2rem;min-width:0;display:grid}.ol-preview-section-name__field--index{max-width:6rem}.ol-preview-section-name__field[hidden]{display:none}.ol-preview-section-name__field-label{color:var(--preview-ol-muted);text-transform:uppercase;letter-spacing:.04em;font-size:.78em}.ol-preview-section-name__type,.ol-preview-section-name__index{box-sizing:border-box;border:1px solid var(--preview-ol-border-current);background:var(--preview-ol-bg);width:100%;min-height:2.1rem;color:inherit;font:inherit;border-radius:.55rem;padding:.3rem .5rem;font-size:.95em}.ol-preview-section-name__type option{background:var(--surface);color:var(--heading)}.ol-preview-section-name__type:focus-visible,.ol-preview-section-name__index:focus-visible{border-color:var(--preview-ol-accent-current);box-shadow:0 0 0 3px var(--accent-halo);outline:none}.ol-preview-section-name__status{color:var(--preview-ol-muted);flex:100%;margin:0;font-size:.82em}.ol-preview-add-section{justify-content:flex-start;margin:.45rem 0 .15rem;display:none}[data-ol-section-editing=enabled] .ol-preview-add-section{display:flex}.open-lyric-render-surface .ol-preview-add-section{display:none!important}.ol-preview-add-section__trigger{appearance:none;border:1px dashed var(--preview-ol-chip-border);background:var(--surface);min-height:2rem;color:var(--preview-ol-accent-current);font:inherit;cursor:pointer;border-radius:999px;justify-content:center;align-items:center;gap:.45rem;padding:.35rem .9rem;font-weight:600;transition:border-color .16s,color .16s,box-shadow .16s,transform .16s;display:inline-flex}.ol-preview-add-section__trigger:before{content:\"+\";font-size:1rem;line-height:1}.ol-preview-add-section__trigger:hover,.ol-preview-add-section__trigger:focus-visible,.ol-preview-add-section__trigger[aria-expanded=true]{border-style:solid;border-color:var(--preview-ol-accent-current);color:var(--preview-ol-accent-current);box-shadow:0 0 0 3px var(--accent-halo);outline:none}.ol-preview-add-section__trigger:active{transform:scale(.98)}.ol-preview-start{border:1px dashed var(--preview-ol-chip-border);background:var(--surface);border-radius:.9rem;flex-direction:column;align-items:flex-start;gap:.55rem;margin:.75rem 0;padding:1.1rem 1.2rem;display:none}[data-ol-section-editing=enabled] .ol-preview-start{display:flex}.open-lyric-render-surface .ol-preview-start{display:none!important}.ol-preview-start__title{color:var(--preview-ol-heading);margin:0;font-size:1.05em;font-weight:700}.ol-preview-start__hint{color:var(--preview-ol-muted);margin:0;font-size:.9em}.ol-preview-start__trigger{appearance:none;border:1px solid var(--preview-ol-accent-current);background:var(--preview-ol-accent-current);min-height:2.25rem;color:var(--surface);font:inherit;cursor:pointer;border-radius:999px;justify-content:center;align-items:center;gap:.45rem;padding:.4rem 1rem;font-weight:600;transition:box-shadow .16s,transform .16s;display:inline-flex}.ol-preview-start__trigger:before{content:\"+\";font-size:1rem;line-height:1}.ol-preview-start__trigger:hover,.ol-preview-start__trigger:focus-visible{box-shadow:0 0 0 3px var(--accent-halo);outline:none}.ol-preview-start__trigger:active{transform:scale(.98)}.ol-preview-add-section-popup{width:min(20rem,100vw - 1.5rem);padding:.7rem}.ol-preview-add-section__form{gap:.55rem;display:grid}.ol-preview-add-section__hint{color:var(--song-view-muted);margin:0;font-size:.82em}.ol-preview-add-section__actions{justify-content:flex-end;display:flex}.ol-preview-add-section__submit{appearance:none;border:1px solid var(--preview-ol-chip-border);background:var(--surface);color:var(--preview-ol-accent-current);font:inherit;cursor:pointer;border-radius:999px;padding:.5rem .9rem;font-weight:600;transition:border-color .16s,color .16s,box-shadow .16s,transform .16s}.ol-preview-add-section__submit:hover,.ol-preview-add-section__submit:focus-visible{border-color:var(--preview-ol-accent-current);box-shadow:0 0 0 3px var(--accent-halo);outline:none}.ol-preview-add-section__submit:active{transform:scale(.98)}.ol-preview-add-section__submit:disabled,.ol-preview-fence__editor-button--save:disabled{opacity:.58;cursor:not-allowed;box-shadow:none}.ol-preview-fence__editor{gap:.5rem;padding:.6rem .7rem .75rem;display:grid}.ol-preview-fence__editor-field{gap:.3rem;display:grid}.ol-preview-fence__editor-input{border:1px solid var(--preview-ol-border-current);background:var(--preview-ol-bg);width:100%;min-height:4.5rem;color:inherit;font:inherit;resize:vertical;white-space:pre;overflow-wrap:normal;border-radius:.6rem;padding:.55rem .65rem;line-height:1.5;overflow-x:auto}.ol-preview-fence__editor-input:focus-visible{border-color:var(--preview-ol-accent-current);box-shadow:0 0 0 3px var(--accent-halo);outline:none}.ol-preview-fence__editor-hint{color:var(--preview-ol-muted);margin:0;font-size:.82em}.ol-preview-fence__editor-actions{flex-wrap:wrap;gap:.4rem;display:flex}.ol-preview-fence__editor-button{appearance:none;border:1px solid var(--preview-ol-border-current);background:var(--preview-ol-bg);color:inherit;font:inherit;cursor:pointer;border-radius:.55rem;padding:.35rem .85rem;font-size:.9em}.ol-preview-fence__editor-button--save{border-color:var(--preview-ol-accent-current);color:var(--preview-ol-accent-current);font-weight:600}.ol-preview-fence__editor-button:focus-visible{box-shadow:0 0 0 3px var(--accent-halo);outline:none}.ol-preview-chord-tools{gap:.45rem;display:grid}.ol-preview-chord-tools__toggle{appearance:none;border:1px solid var(--preview-ol-border-current);background:var(--preview-ol-bg);min-height:2.25rem;color:var(--preview-ol-accent-current);font:inherit;cursor:pointer;border-radius:999px;justify-self:start;align-items:center;gap:.35rem;padding:.3rem .8rem;font-size:.9em;font-weight:600;display:inline-flex}.ol-preview-chord-tools__toggle[aria-expanded=true]{border-color:var(--preview-ol-accent-current)}.ol-preview-chord-tools__toggle:focus-visible,.ol-preview-chord-picker__chip:focus-visible,.ol-preview-chord-picker__insert:focus-visible,.ol-preview-chord-picker__bass-select:focus-visible{box-shadow:0 0 0 3px var(--accent-halo);outline:none}.ol-preview-chord-picker{border:1px solid var(--preview-ol-border-current);background:var(--preview-ol-bg);border-radius:.6rem;gap:.6rem;padding:.6rem .65rem;display:grid}.ol-preview-chord-picker[hidden]{display:none!important}.ol-preview-chord-picker__group,.ol-preview-chord-picker__builder{gap:.35rem;display:grid}.ol-preview-chord-picker__heading{color:var(--preview-ol-muted);letter-spacing:.02em;text-transform:uppercase;margin:0;font-size:.78em;font-weight:600}.ol-preview-chord-picker__options{flex-wrap:wrap;gap:.3rem;display:flex}.ol-preview-chord-picker__chip{appearance:none;border:1px solid var(--preview-ol-border-current);background:var(--surface);min-width:2.5rem;min-height:2.25rem;color:inherit;font:inherit;cursor:pointer;border-radius:.5rem;padding:.25rem .55rem;font-size:.9em}.ol-preview-chord-picker__chip--chord{color:var(--preview-ol-accent-current);font-weight:600}.ol-preview-chord-picker__chip:hover{border-color:var(--preview-ol-accent-current)}.ol-preview-chord-picker__chip[aria-pressed=true]{border-color:var(--preview-ol-accent-current);background:color-mix(in srgb, var(--preview-ol-accent-current) 18%, var(--surface));color:var(--preview-ol-accent-current);font-weight:600}.ol-preview-chord-picker__builder-footer{flex-wrap:wrap;align-items:center;gap:.5rem;display:flex}.ol-preview-chord-picker__bass{align-items:center;gap:.35rem;font-size:.88em;display:inline-flex}.ol-preview-chord-picker__bass-select{border:1px solid var(--preview-ol-border-current);background:var(--surface);min-height:2.25rem;color:inherit;font:inherit;border-radius:.5rem;padding:.2rem .4rem}.ol-preview-chord-picker__insert{appearance:none;border:1px solid var(--preview-ol-accent-current);background:var(--surface);min-height:2.25rem;color:var(--preview-ol-accent-current);font:inherit;cursor:pointer;border-radius:.55rem;padding:.3rem .9rem;font-size:.9em;font-weight:600}.ol-preview-chord-picker__insert:disabled{border-color:var(--preview-ol-border-current);color:var(--preview-ol-muted);cursor:not-allowed}.ol-preview-chord-picker__status{color:var(--preview-ol-muted);margin:0;font-size:.82em}.ol-preview-config__text-value{align-items:baseline;gap:.3rem;max-width:100%;display:inline-flex}.ol-preview-config__text-display{border-radius:.35rem}.ol-preview-config__text-display[hidden]{display:none!important}[data-ol-section-editing=enabled] .ol-preview-config__text-display{cursor:text;transition:background-color .16s}[data-ol-section-editing=enabled] .ol-preview-config__text-display:hover{background:var(--preview-ol-bg)}[data-ol-section-editing=enabled] .ol-preview-config__text-display--empty:after{content:attr(data-config-empty-label);color:var(--preview-ol-muted);font-style:italic}.ol-preview-config__text-edit{appearance:none;width:1.4rem;height:1.4rem;color:var(--preview-ol-heading);cursor:pointer;opacity:.45;background:0 0;border:1px solid #0000;border-radius:.4rem;flex:none;justify-content:center;align-items:center;padding:0;transition:opacity .16s,background-color .16s,border-color .16s,color .16s;display:none}.ol-preview-config__text-edit svg{width:.75rem;height:.75rem}[data-ol-section-editing=enabled] .ol-preview-config__text-edit{display:inline-flex}.ol-preview-config__text-edit[hidden],.open-lyric-render-surface .ol-preview-config__text-edit{display:none!important}.ol-preview-config__entry:hover .ol-preview-config__text-edit,.ol-preview-config__text-edit:hover,.ol-preview-config__text-edit:focus-visible{opacity:1}.ol-preview-config__text-edit:hover{border-color:var(--preview-ol-border-current);background:var(--preview-ol-bg);color:var(--preview-ol-accent-current)}.ol-preview-config__text-edit:focus-visible{box-shadow:0 0 0 3px var(--accent-halo);outline:none}.ol-preview-config__text-editor{flex-wrap:wrap;align-items:center;gap:.35rem;width:100%;display:inline-flex}.ol-preview-config__text-editor-input{border:1px solid var(--preview-ol-border-current);background:var(--preview-ol-bg);min-width:0;color:inherit;font:inherit;border-radius:.45rem;flex:12rem;padding:.25rem .45rem}.ol-preview-config__text-editor-input:focus-visible{border-color:var(--preview-ol-accent-current);box-shadow:0 0 0 3px var(--accent-halo);outline:none}.ol-preview-config__text-editor-actions{flex:none;gap:.3rem;display:inline-flex}.ol-preview-config__text-editor-button{appearance:none;border:1px solid var(--preview-ol-border-current);background:var(--preview-ol-bg);color:inherit;font:inherit;cursor:pointer;border-radius:.45rem;padding:.22rem .6rem;font-size:.85em}.ol-preview-config__text-editor-button--save{border-color:var(--preview-ol-accent-current);color:var(--preview-ol-accent-current);font-weight:600}.ol-preview-config__text-editor-button:focus-visible{box-shadow:0 0 0 3px var(--accent-halo);outline:none}@media print{.ol-preview-fence__edit,.ol-preview-fence__editor,.ol-preview-config__text-edit,.ol-preview-config__text-editor{display:none!important}}.ol-preview-lines{gap:.45rem;display:grid}.ol-preview-line{white-space:pre-wrap;word-break:break-word;margin-left:1rem;margin-right:1rem}.ol-preview-line--comment{color:var(--preview-ol-muted);opacity:.85;font-style:italic}.ol-song-view .ol-preview-line--comment{color:var(--song-view-muted)}.ol-preview-line--chorded{white-space:normal;word-break:normal}.ol-preview-line__content--chorded{white-space:normal;min-width:0;display:block}.ol-preview-line__content--progression{vertical-align:top;max-width:100%;display:inline-block}.ol-preview-lyric-segment{vertical-align:top;grid-template-rows:auto auto;max-width:100%;display:inline-grid}.ol-preview-line--measuring-intrinsic .ol-preview-line__content--chorded{width:max-content;max-width:none}.ol-preview-line--measuring-intrinsic .ol-preview-lyric-segment{max-width:none}.ol-preview-line--measuring-intrinsic .ol-preview-lyric-segment__chord,.ol-preview-line--measuring-intrinsic .ol-preview-lyric-segment__text{white-space:pre}.ol-preview-chord{appearance:none;color:var(--accent);cursor:pointer;font-size:.7em;line-height:inherit;white-space:nowrap;background:0 0;border:0;border-radius:.3rem;margin:0;padding:0;transition:background .16s,box-shadow .16s,color .16s}.ol-preview-chord--with-brackets{align-items:baseline;gap:0;display:inline-flex}.ol-preview-chord--hidden{display:none}.ol-preview-chord__bracket{color:#0000;user-select:none}.ol-preview-chord:hover,.ol-preview-chord:focus-visible{background:var(--preview-ol-chip-bg);box-shadow:0 0 0 1px var(--preview-ol-chip-border);color:var(--preview-ol-accent-current);outline:none}.ol-chord-popup{--ol-chord-popup-pointer-x:50%;--ol-chord-popup-main-diagram-width:124px;--ol-chord-popup-variant-scale:.3;z-index:50;border:1px solid var(--chord-popup-border);background:var(--chord-popup-bg);width:min(136.5px,100vw - 24px);box-shadow:var(--chord-popup-shadow);color:var(--ink);pointer-events:none;opacity:0;border-radius:1rem;padding:.3rem;transition:opacity .12s,transform .12s;position:fixed;top:0;left:0;transform:translateY(6px)scale(.98)}.ol-chord-popup[data-content-type=pattern]{width:min(22rem,100vw - 24px)}.ol-chord-popup.is-visible{opacity:1;pointer-events:auto;transform:translateY(0)scale(1)}.ol-chord-popup:after{content:\"\";left:var(--ol-chord-popup-pointer-x);border:1px solid var(--chord-popup-border);background:var(--surface);width:12px;height:12px;position:absolute;transform:translate(-50%)rotate(45deg)}.ol-chord-popup[data-placement=bottom]:after{border-bottom:0;border-right:0;top:-7px}.ol-chord-popup[data-placement=top]:after{border-top:0;border-left:0;bottom:-7px}.ol-chord-popup__name,.ol-chord-popup__description,.ol-chord-popup__variants-count,.ol-chord-popup__variants-heading,.ol-chord-popup__variant-label,.ol-chord-popup__status{margin:0}.ol-chord-popup__header{flex-wrap:wrap;align-items:baseline;gap:.18rem;line-height:1.15;display:flex}.ol-chord-popup__actions:not([hidden]){align-self:center;align-items:center;gap:.2rem;margin-left:auto;display:inline-flex}.ol-chord-popup:has(>.ol-chord-popup__panel:not([hidden]))>:is(.ol-chord-popup__diagram,.ol-chord-popup__variants,.ol-chord-popup__status){display:none}.ol-chord-popup__name{letter-spacing:.01em;font-size:.72rem;font-weight:500}.ol-chord-popup__description{color:var(--song-view-muted);font-size:.68rem;line-height:1.2}.ol-chord-popup__description:before{content:\":\";color:var(--song-view-muted);margin-right:.18rem}.ol-chord-popup__diagram{border:1px solid var(--chord-popup-diagram-border);background:var(--chord-popup-diagram-bg);min-height:8.5rem;box-shadow:var(--chord-popup-diagram-shadow);border-radius:.95rem;justify-items:center;margin-top:.38rem;display:grid;overflow:hidden}.ol-chord-popup[data-content-type=pattern] .ol-chord-popup__diagram{justify-items:stretch;min-height:0;padding:.45rem;overflow:visible}.ol-chord-popup__diagram>svg{width:100%;max-width:var(--ol-chord-popup-main-diagram-width);user-select:none;cursor:pointer;height:auto;display:block}.ol-chord-popup__variants{border-top:1px solid var(--line);padding-top:.1rem}.ol-chord-popup__variants-header{justify-content:space-between;align-items:baseline;gap:.5rem;font-size:.4rem;display:flex}.ol-chord-popup__variants-heading{color:var(--song-view-muted);letter-spacing:.12em;text-transform:uppercase}.ol-chord-popup__variants-count{color:var(--song-view-muted);line-height:1.2}.ol-chord-popup__variants-carousel{grid-template-columns:auto minmax(0,1fr) auto;align-items:center;gap:.45rem;margin-top:.3rem;display:grid}.ol-chord-popup__variants-nav{border:1px solid var(--line);background:var(--surface);width:1.85rem;height:1.85rem;color:var(--heading);cursor:pointer;border-radius:999px;justify-content:center;align-items:center;padding:0;transition:border-color .12s,color .12s,box-shadow .12s,transform .12s;display:inline-flex}.ol-chord-popup__variants-nav:hover,.ol-chord-popup__variants-nav:focus-visible{border-color:var(--accent);color:var(--accent);box-shadow:0 0 0 3px var(--accent-halo);outline:none}.ol-chord-popup__variants-nav:active{transform:scale(.96)}.ol-chord-popup__variants-nav:disabled{opacity:.42;cursor:default;box-shadow:none;color:var(--song-view-muted)}.ol-chord-popup__variants-viewport{min-width:0;overflow:hidden}.ol-chord-popup__variants-track{will-change:transform;transition:transform .18s;display:flex}.ol-chord-popup__variant{appearance:none;border:1px solid var(--line);background:var(--surface);width:100%;min-width:0;color:inherit;cursor:pointer;font:inherit;text-align:inherit;border-radius:.8rem;flex:0 0 100%;justify-items:center;gap:.22rem;margin:0;padding:.28rem .2rem .3rem;transition:border-color .12s,box-shadow .12s,transform .12s,background-color .12s;display:grid}.ol-chord-popup__variant:hover,.ol-chord-popup__variant:focus-visible{border-color:var(--accent);box-shadow:0 0 0 3px var(--accent-halo);outline:none}.ol-chord-popup__variant:active{transform:scale(.98)}:root{--monaco-popup-viewport-width:100vw;--monaco-popup-viewport-height:100dvh;--monaco-popup-viewport-margin:12px}body>.overflowingContentWidgets,body>.overflowingOverlayWidgets,.context-view.monaco-component,.context-view.monaco-menu-container{z-index:25}.context-view.monaco-component .action-widget{min-width:min(26rem,100vw - 1.5rem);max-width:min(44rem,100vw - 1.5rem)}.context-view.monaco-component .action-widget .monaco-list .monaco-list-row.action{gap:.5rem}.context-view.monaco-component .action-widget .monaco-list-row.action .title{text-overflow:clip;flex:0 auto;min-width:0;overflow:visible}.context-view.monaco-component .action-widget .monaco-list-row.action .description{flex:none}@media (width<=992px){:root{--monaco-mobile-popup-max-width:calc(var(--monaco-popup-viewport-width) - (var(--monaco-popup-viewport-margin) * 2));--monaco-mobile-popup-max-height:calc(var(--monaco-popup-viewport-height) - (var(--monaco-popup-viewport-margin) * 2))}body>.overflowingContentWidgets,body>.overflowingOverlayWidgets,.context-view.monaco-component,.context-view.monaco-menu-container,.monaco-submenu.context-view{max-width:var(--monaco-mobile-popup-max-width);max-height:var(--monaco-mobile-popup-max-height)}.context-view.monaco-menu-container,.context-view.monaco-menu-container .monaco-menu,.monaco-submenu.context-view,.monaco-submenu.context-view .monaco-menu{box-sizing:border-box;width:min(26rem, var(--monaco-mobile-popup-max-width));max-width:var(--monaco-mobile-popup-max-width);max-height:calc(var(--monaco-mobile-popup-max-height) - 8px);overscroll-behavior:contain;overflow-y:auto}.context-view.monaco-menu-container .monaco-action-bar.vertical,.monaco-submenu.context-view .monaco-action-bar.vertical{box-sizing:border-box;max-height:calc(var(--monaco-mobile-popup-max-height) - 8px);overscroll-behavior:contain;overflow-y:auto}.context-view.monaco-menu-container .monaco-action-bar.vertical .actions-container,.monaco-submenu.context-view .monaco-action-bar.vertical .actions-container,.context-view.monaco-menu-container .monaco-action-bar.vertical .action-item,.monaco-submenu.context-view .monaco-action-bar.vertical .action-item,.context-view.monaco-menu-container .monaco-action-bar.vertical .action-menu-item,.monaco-submenu.context-view .monaco-action-bar.vertical .action-menu-item{min-width:0}.context-view.monaco-menu-container .monaco-action-bar.vertical .actions-container,.monaco-submenu.context-view .monaco-action-bar.vertical .actions-container{max-height:calc(var(--monaco-mobile-popup-max-height) - 8px);overscroll-behavior:contain;overflow-y:auto}.context-view.monaco-menu-container .monaco-action-bar.vertical .action-menu-item,.monaco-submenu.context-view .monaco-action-bar.vertical .action-menu-item{align-items:flex-start;height:auto;min-height:2.5rem}.context-view.monaco-menu-container .monaco-action-bar.vertical .action-label:not(.separator),.monaco-submenu.context-view .monaco-action-bar.vertical .action-label:not(.separator),.context-view.monaco-menu-container .monaco-action-bar.vertical .keybinding,.monaco-submenu.context-view .monaco-action-bar.vertical .keybinding{box-sizing:border-box;white-space:normal;overflow-wrap:anywhere;word-break:break-word;min-width:0;max-width:100%;max-height:none;padding-top:.55rem;padding-bottom:.55rem}.context-view.monaco-menu-container .monaco-action-bar.vertical .action-label:not(.separator),.monaco-submenu.context-view .monaco-action-bar.vertical .action-label:not(.separator){flex:1 1 0}.context-view.monaco-menu-container .monaco-action-bar.vertical .keybinding,.monaco-submenu.context-view .monaco-action-bar.vertical .keybinding{text-align:right;flex:0 8.5rem;justify-content:flex-end;align-self:stretch;align-items:center;display:flex}.context-view.monaco-menu-container .monaco-action-bar.vertical .submenu-indicator,.monaco-submenu.context-view .monaco-action-bar.vertical .submenu-indicator{flex:none;align-self:stretch;align-items:center;padding:0 1rem 0 .5rem;display:flex}.context-view.monaco-menu-container .monaco-action-bar.vertical .submenu-indicator.codicon:before,.monaco-submenu.context-view .monaco-action-bar.vertical .submenu-indicator.codicon:before{margin-right:0}.context-view.monaco-menu-container .monaco-action-bar.vertical .menu-item-check{align-self:stretch}body>.overflowingContentWidgets .suggest-widget,body>.overflowingOverlayWidgets .suggest-widget,body>.overflowingContentWidgets .suggest-details,body>.overflowingOverlayWidgets .suggest-details,body>.overflowingContentWidgets .monaco-hover,body>.overflowingOverlayWidgets .monaco-hover,body>.overflowingContentWidgets .parameter-hints-widget,body>.overflowingOverlayWidgets .parameter-hints-widget,.context-view.monaco-component .action-widget,.monaco-editor .find-widget,.monaco-editor .marker-widget{box-sizing:border-box;max-width:var(--monaco-mobile-popup-max-width)!important;max-height:var(--monaco-mobile-popup-max-height)!important}body>.overflowingContentWidgets .suggest-widget>.tree,body>.overflowingOverlayWidgets .suggest-widget>.tree,body>.overflowingContentWidgets .suggest-details>.monaco-scrollable-element,body>.overflowingOverlayWidgets .suggest-details>.monaco-scrollable-element,body>.overflowingContentWidgets .monaco-hover .monaco-scrollable-element,body>.overflowingOverlayWidgets .monaco-hover .monaco-scrollable-element,.context-view.monaco-component .action-widget .monaco-list{max-height:calc(var(--monaco-mobile-popup-max-height) - 2px)!important}body>.overflowingContentWidgets .suggest-details,body>.overflowingOverlayWidgets .suggest-details,body>.overflowingContentWidgets .monaco-hover .hover-contents,body>.overflowingOverlayWidgets .monaco-hover .hover-contents,body>.overflowingContentWidgets .parameter-hints-widget .body,body>.overflowingOverlayWidgets .parameter-hints-widget .body,.context-view.monaco-component .action-widget .title,.monaco-editor .marker-widget .descriptioncontainer{overflow-wrap:anywhere;word-break:break-word}body>.overflowingContentWidgets .monaco-hover .hover-row.status-bar,body>.overflowingOverlayWidgets .monaco-hover .hover-row.status-bar,.monaco-editor .monaco-hover .hover-row.status-bar{flex-wrap:wrap}body>.overflowingContentWidgets .monaco-hover .hover-row.status-bar .info,body>.overflowingOverlayWidgets .monaco-hover .hover-row.status-bar .info,.monaco-editor .monaco-hover .hover-row.status-bar .info{flex:auto;min-width:0}body>.overflowingContentWidgets .monaco-hover .hover-row.status-bar .actions,body>.overflowingOverlayWidgets .monaco-hover .hover-row.status-bar .actions,.monaco-editor .monaco-hover .hover-row.status-bar .actions{flex-wrap:wrap;flex:100%;gap:.35rem .75rem;width:auto;min-width:0;padding-top:.35rem;padding-bottom:.45rem}body>.overflowingContentWidgets .monaco-hover .hover-row.status-bar .actions .action-container,body>.overflowingOverlayWidgets .monaco-hover .hover-row.status-bar .actions .action-container,.monaco-editor .monaco-hover .hover-row.status-bar .actions .action-container{text-wrap:wrap;text-overflow:clip;min-width:0;max-width:100%;margin-right:0;overflow:visible}body>.overflowingContentWidgets .monaco-hover .hover-row.status-bar .actions .action-container a,body>.overflowingOverlayWidgets .monaco-hover .hover-row.status-bar .actions .action-container a,.monaco-editor .monaco-hover .hover-row.status-bar .actions .action-container a{white-space:normal;overflow-wrap:anywhere}.context-view.monaco-component .action-widget{min-width:min(26rem, var(--monaco-mobile-popup-max-width))}.context-view.monaco-component .action-widget .monaco-list-row.action .title{white-space:normal}.monaco-editor .view-overlays .current-line{background-color:#1f2a3703!important}.monaco-editor .view-overlays .current-line.current-line-exact{border-color:#1f2a3708!important}:root[data-theme^=dark] .monaco-editor .view-overlays .current-line{background-color:#e5edf505!important}:root[data-theme^=dark] .monaco-editor .view-overlays .current-line.current-line-exact{border-color:#e5edf50a!important}.monaco-editor .find-widget{left:var(--monaco-popup-viewport-margin)!important;max-width:var(--monaco-mobile-popup-max-width)!important;right:auto!important}.monaco-editor .marker-widget{white-space:normal}}.ol-chord-popup__variant-diagram{width:100%;min-height:calc(8.5rem * var(--ol-chord-popup-variant-scale));border:1px solid var(--chord-popup-diagram-border);background:var(--chord-popup-diagram-bg);box-shadow:var(--chord-popup-diagram-shadow);border-radius:.72rem;justify-items:center;padding:.14rem .08rem .04rem;display:grid}.ol-chord-popup__variant-diagram>svg{width:100%;max-width:calc(var(--ol-chord-popup-main-diagram-width) * var(--ol-chord-popup-variant-scale));height:auto;display:block}.ol-chord-popup__variant-label{color:var(--song-view-muted);text-align:center;font-size:.52rem;line-height:1.25}.ol-chord-popup__status{color:var(--song-view-muted);text-align:center;margin-top:.35rem;font-size:.76rem;line-height:1.25}.ol-chord-popup__pattern-preview{width:100%}.ol-chord-popup__pattern-grid-shell{border-radius:.78rem;overflow:hidden}.ol-chord-popup[data-content-type=pattern] .ol-song-view__pattern-display{border-radius:.72rem;padding:.18rem .18rem .3rem}.ol-chord-popup[data-content-type=pattern] .ol-song-view__pattern-row{grid-template-columns:repeat(var(--pattern-column-count), minmax(1.2rem, 1fr))}.ol-preview-lyric-segment__chord,.ol-preview-lyric-segment__text{display:block}.ol-preview-lyric-segment__text{white-space:pre-wrap;overflow-wrap:break-word}.ol-preview-lyric-segment__chord{white-space:pre;min-height:1.25em}.ol-preview-lyric-segment__chord .ol-preview-bar--hidden,.ol-preview-lyric-segment__chord .ol-preview-chord__bracket:first-child{display:none}.ol-preview-lyric-segment__chord .ol-preview-bar:not(.ol-preview-bar--hidden){margin-right:.2em}.ol-preview-lyric-segment__chord--empty{visibility:hidden}.ol-preview-lyric-segment__chord--hidden{display:none}.ol-preview-bar{color:var(--preview-ol-muted)}.ol-preview-bar--hidden{visibility:hidden}.ol-preview-directive{color:var(--preview-ol-token);font-weight:400}.ol-preview-pattern-reference{appearance:none;color:var(--preview-ol-accent-current);cursor:pointer;font:inherit;font-weight:500;line-height:inherit;text-underline-offset:.12em;white-space:nowrap;background:0 0;border:none;border-radius:.38rem;align-items:center;margin:0 .05rem;padding:0 .2rem;text-decoration:underline 1px;display:inline-flex}.ol-preview-pattern-reference:hover,.ol-preview-pattern-reference:focus-visible{background:var(--preview-ol-chip-bg);box-shadow:0 0 0 1px var(--preview-ol-chip-border);outline:none}.ol-preview-repeat{border:1px solid var(--preview-repeat-border);background:var(--preview-repeat-bg);color:var(--preview-repeat-text);white-space:nowrap;border-radius:999px;align-items:center;margin-left:.5rem;padding:.01rem .2rem;font-size:.65em;line-height:1.3;display:inline-flex}.ol-preview-structure-line{flex-wrap:wrap;align-items:center;gap:.45rem;display:flex}.ol-preview-structure-link{flex:none;align-items:center;gap:.45rem;display:inline-flex}.ol-preview-structure-step-shell{align-items:center;display:inline-flex;position:relative}.ol-preview-structure-step{border:1px solid var(--preview-ol-step-border,var(--preview-ol-chip-border));background:var(--preview-ol-step-bg,var(--preview-ol-chip-bg));color:var(--preview-ol-step-text,var(--preview-ol-heading));white-space:nowrap;border-radius:999px;flex:none;align-items:center;padding:.28em .65em;font-size:.92em;text-decoration:none;display:inline-flex}.ol-preview-structure-repeat-controls{opacity:0;pointer-events:none;z-index:2;gap:.18rem;transition:opacity .16s,transform .16s;display:inline-flex;position:absolute;top:-.6rem;right:-.4rem;transform:translateY(-.12rem)scale(.96)}.ol-preview-structure-step-shell:hover .ol-preview-structure-repeat-controls,.ol-preview-structure-step-shell:focus-within .ol-preview-structure-repeat-controls{opacity:1;pointer-events:auto;transform:translateY(0)scale(1)}.ol-preview-structure-repeat-button{appearance:none;border:1px solid var(--preview-ol-chip-border);background:var(--surface);width:1.35rem;height:1.35rem;color:var(--preview-ol-accent-current);font:inherit;cursor:pointer;border-radius:999px;justify-content:center;align-items:center;padding:0;font-size:.78rem;line-height:1;transition:border-color .16s,color .16s,box-shadow .16s,transform .16s;display:inline-flex;box-shadow:0 8px 18px #1019231f}.ol-preview-structure-repeat-button:hover,.ol-preview-structure-repeat-button:focus-visible{border-color:var(--preview-ol-accent-current);color:var(--preview-ol-accent-current);box-shadow:0 0 0 3px var(--accent-halo);outline:none}.ol-preview-structure-repeat-button:active{transform:scale(.96)}.ol-preview-structure-repeat-button:disabled{color:var(--song-view-muted);cursor:not-allowed;opacity:.72;box-shadow:0 6px 14px #10192314}a.ol-preview-structure-step{cursor:pointer}a.ol-preview-structure-step:hover,a.ol-preview-structure-step:focus-visible{box-shadow:0 0 0 2px var(--accent-halo);outline:none}.ol-preview-structure-arrow{color:var(--preview-ol-muted);flex:none;justify-content:center;align-items:center;line-height:1;display:inline-flex}.ol-preview-structure-arrow-button{appearance:none;font:inherit;cursor:pointer;background:0 0;border:none;border-radius:999px;padding:.14rem .28rem;line-height:1;transition:color .16s,background .16s,box-shadow .16s,transform .16s}.ol-preview-structure-arrow-button:hover,.ol-preview-structure-arrow-button:focus-visible,.ol-preview-structure-arrow-button[aria-expanded=true]{color:var(--preview-ol-accent-current);background:var(--preview-ol-chip-bg);box-shadow:0 0 0 3px var(--accent-halo);outline:none}.ol-preview-structure-arrow-button:active{transform:scale(.96)}.ol-preview-config-shell{gap:.7rem;display:grid}.ol-preview-config{margin:0;display:block}.ol-preview-config__missing-actions{justify-content:flex-start;display:flex}.ol-preview-config__add-button{appearance:none;border:1px solid var(--preview-ol-chip-border);background:var(--surface);min-height:2rem;color:var(--preview-ol-accent-current);font:inherit;cursor:pointer;border-radius:999px;justify-content:center;align-items:center;gap:.45rem;padding:.35rem .85rem;font-weight:600;transition:border-color .16s,color .16s,box-shadow .16s,transform .16s;display:inline-flex;box-shadow:0 8px 18px #1019231f}.ol-preview-config__add-button:before{content:\"+\";font-size:1rem;line-height:1}.ol-preview-config__add-button:hover,.ol-preview-config__add-button:focus-visible,.ol-preview-config__add-button[aria-expanded=true]{border-color:var(--preview-ol-accent-current);color:var(--preview-ol-accent-current);box-shadow:0 0 0 3px var(--accent-halo);outline:none}.ol-preview-config__add-button:active{transform:scale(.98)}.ol-preview-config__entry{margin:0 0 .65rem}.ol-preview-config__entry:last-child{margin-bottom:0}.ol-preview-config__entry--inline{box-sizing:border-box;flex-wrap:wrap;align-items:flex-start;gap:.2rem .45rem;width:100%;display:flex}.ol-preview-config__key{color:var(--preview-ol-heading);margin:0}.ol-preview-config__value{margin:0}.ol-preview-config__field-control{align-items:center;min-width:0;max-width:100%;display:inline-flex}.ol-preview-config__key-trigger{font-size:inherit}.ol-preview-config__key-trigger[aria-expanded=true]{background:var(--preview-ol-chip-bg);box-shadow:0 0 0 1px var(--preview-ol-chip-border);color:var(--preview-ol-accent-current)}.ol-preview-config__key-trigger--empty{color:var(--song-view-muted);font-style:italic}.ol-preview-config__tempo-trigger,.ol-preview-config__time-trigger{appearance:none;color:inherit;font:inherit;cursor:pointer;background:0 0;border:none;padding:0}.ol-preview-config__tempo-trigger:hover,.ol-preview-config__tempo-trigger:focus-visible,.ol-preview-config__tempo-trigger[aria-expanded=true],.ol-preview-config__time-trigger:hover,.ol-preview-config__time-trigger:focus-visible,.ol-preview-config__time-trigger[aria-expanded=true]{color:var(--preview-ol-accent-current);outline:none}.ol-preview-config__tempo-trigger--empty,.ol-preview-config__time-trigger--empty{color:var(--song-view-muted);font-style:italic}.ol-preview-config__tempo-trigger:focus-visible,.ol-preview-config__time-trigger:focus-visible{box-shadow:0 2px 0 0 var(--accent-halo)}.ol-preview-config__tempo-suffix{color:var(--song-view-muted);letter-spacing:.08em;text-transform:uppercase;margin-left:.28rem;font-size:.78rem}.ol-preview-config-tempo-popup{gap:.55rem;width:min(14rem,100vw - 1.5rem);min-width:min(12rem,100vw - 1.5rem);padding:.65rem .7rem .6rem}.ol-preview-config__tempo-popup-value{justify-content:center;align-items:baseline;gap:.28rem;display:inline-flex}.ol-preview-config__tempo-popup-output{color:var(--heading);font-size:1.3rem;font-weight:700;line-height:1}.ol-preview-config__tempo-popup-suffix{color:var(--song-view-muted);letter-spacing:.08em;text-transform:uppercase;font-size:.8rem}.ol-preview-config__tempo-range{width:100%;accent-color:var(--preview-ol-accent-current);cursor:pointer;margin:0}.ol-preview-config__tempo-range:focus-visible{outline:none}.ol-preview-config__tempo-scale{color:var(--song-view-muted);justify-content:space-between;align-items:center;font-size:.76rem;display:flex}.ol-preview-config__locales-value{min-height:2rem;padding-right:2.8rem;position:relative}.ol-preview-config__locales-value--empty{align-items:center;display:flex}.ol-preview-config__locales-value--empty .ol-preview-config__part-action{opacity:1;pointer-events:auto;transform:translateY(0)scale(1)}.ol-preview-config__locales-list{flex-wrap:wrap;align-items:center;gap:.3rem;display:flex}.ol-preview-config__locale-item{border:1px solid var(--preview-ol-chip-border);background:var(--surface);white-space:nowrap;border-radius:999px;align-items:center;gap:.1rem;padding:.1rem .15rem .1rem .6rem;line-height:1.5;display:inline-flex}.ol-preview-config__locale-name{font-variant-numeric:tabular-nums}.ol-preview-config__locale-remove{appearance:none;color:red;cursor:pointer;opacity:0;pointer-events:none;background:0 0;border:0;border-radius:999px;flex:none;justify-content:center;align-items:center;width:1.15rem;height:1.15rem;padding:0;transition:opacity .16s,transform .16s,color .16s;display:inline-flex;transform:scale(.92)}.ol-preview-config__locale-remove:before{content:\"×\";font-size:.92rem;line-height:1}.ol-preview-config__locale-item:hover .ol-preview-config__locale-remove,.ol-preview-config__locale-item:focus-within .ol-preview-config__locale-remove{opacity:1;pointer-events:auto;transform:scale(1)}.ol-preview-config__locale-remove:focus-visible{color:var(--preview-ol-accent-current);box-shadow:0 0 0 3px var(--accent-halo);outline:none}.ol-preview-config__locale-remove:active{transform:scale(.94)}.ol-preview-config__locales-action{justify-items:end;gap:.4rem;display:grid;position:absolute;top:0;right:0}.ol-preview-config__attachments-value{min-height:2rem;padding-right:2.8rem;position:relative}.ol-preview-config__attachments-value--empty{align-items:center;display:flex}.ol-preview-config__attachments-value--empty .ol-preview-config__part-action{opacity:1;pointer-events:auto;transform:translateY(0)scale(1)}.ol-preview-config__attachments-list{gap:.35rem;padding-right:.2rem;display:grid}.ol-preview-config__attachment-item{word-break:break-word;align-items:flex-start;gap:.45rem;min-width:0;display:flex}.ol-preview-config__attachment-item a{overflow-wrap:anywhere;min-width:0;max-width:100%}.ol-preview-config__attachment-url{color:var(--muted);font-size:.9em}.ol-preview-config__attachment-remove{appearance:none;border:1px solid var(--preview-ol-chip-border);background:var(--surface);color:red;cursor:pointer;opacity:0;pointer-events:none;border-radius:999px;flex:none;justify-content:center;align-items:center;width:1.45rem;height:1.45rem;margin-top:.02rem;padding:0;transition:opacity .16s,transform .16s,border-color .16s,color .16s,box-shadow .16s;display:inline-flex;transform:scale(.92);box-shadow:0 8px 18px #1019231f}.ol-preview-config__attachment-remove:before{content:\"×\";font-size:.98rem;line-height:1}.ol-preview-config__attachment-item:hover .ol-preview-config__attachment-remove,.ol-preview-config__attachment-item:focus-within .ol-preview-config__attachment-remove{opacity:1;pointer-events:auto;transform:scale(1)}.ol-preview-config__attachment-remove:focus-visible{border-color:var(--preview-ol-accent-current);color:var(--preview-ol-accent-current);box-shadow:0 0 0 3px var(--accent-halo);outline:none}.ol-preview-config__attachment-remove:hover{border-color:var(--preview-ol-accent-current)}.ol-preview-config__attachment-remove:active{transform:scale(.96)}.ol-preview-config__attachments-action{justify-items:end;gap:.4rem;display:grid;position:absolute;top:0;right:0}.ol-preview-config__value--structure{position:relative}.ol-preview-config__structure-value{min-height:2rem;padding-right:2.8rem;position:relative}.ol-preview-config__structure-value--empty{align-items:center;display:flex}.ol-preview-config__structure-value--empty .ol-preview-config__part-action{opacity:1;pointer-events:auto;transform:translateY(0)scale(1)}.ol-preview-config__patterns-value{min-height:2rem;padding-right:2.8rem;position:relative}.ol-preview-config__patterns-value--empty .ol-preview-config__part-action{opacity:1;pointer-events:auto;transform:translateY(0)scale(1)}.ol-preview-config__patterns-action{justify-items:end;gap:.4rem;display:grid;position:absolute;top:0;right:0}.ol-preview-config__pattern-grid{padding-right:.2rem}.ol-preview-config__pattern-card .ol-song-view__pattern-header{justify-content:flex-start}.ol-preview-config__pattern-actions{opacity:0;pointer-events:none;align-items:center;gap:.35rem;margin-left:auto;transition:opacity .16s,transform .16s;display:inline-flex;transform:translateY(-.12rem)}.ol-preview-config__pattern-card:hover .ol-preview-config__pattern-actions,.ol-preview-config__pattern-card:focus-within .ol-preview-config__pattern-actions{opacity:1;pointer-events:auto;transform:translateY(0)}.ol-preview-config__pattern-duplicate,.ol-preview-config__pattern-remove{appearance:none;border:1px solid var(--preview-ol-chip-border);background:var(--surface);width:1.45rem;height:1.45rem;color:var(--preview-ol-accent-current);font:inherit;cursor:pointer;border-radius:999px;justify-content:center;align-items:center;padding:0;font-size:.92rem;line-height:1;transition:border-color .16s,color .16s,box-shadow .16s,transform .16s;display:inline-flex;box-shadow:0 8px 18px #1019231f}.ol-preview-config__pattern-remove{color:red}.ol-preview-config__pattern-duplicate-icon{width:.72rem;height:.72rem;display:block;position:relative}.ol-preview-config__pattern-duplicate-icon:before,.ol-preview-config__pattern-duplicate-icon:after{content:\"\";border:1.5px solid;border-radius:.12rem;width:.48rem;height:.48rem;position:absolute}.ol-preview-config__pattern-duplicate-icon:before{top:.02rem;left:.2rem}.ol-preview-config__pattern-duplicate-icon:after{background:var(--surface);top:.2rem;left:.02rem}.ol-preview-config__pattern-duplicate:hover,.ol-preview-config__pattern-duplicate:focus-visible,.ol-preview-config__pattern-remove:hover,.ol-preview-config__pattern-remove:focus-visible{border-color:var(--preview-ol-accent-current);box-shadow:0 0 0 3px var(--accent-halo);outline:none}.ol-preview-config__pattern-duplicate:active,.ol-preview-config__pattern-remove:active{transform:scale(.96)}.ol-preview-config__structure-action{justify-items:end;gap:.4rem;display:grid;position:absolute;top:0;right:0}.ol-preview-config__part-action{border:1px solid var(--preview-ol-chip-border);background:var(--surface);width:1.9rem;height:1.9rem;color:var(--accent);font:inherit;cursor:pointer;opacity:0;pointer-events:none;border-radius:999px;justify-content:center;align-items:center;padding:0;font-size:1.15rem;line-height:1;transition:opacity .16s,transform .16s,box-shadow .16s,border-color .16s,color .16s;display:inline-flex;transform:translateY(-.12rem)scale(.94);box-shadow:0 8px 20px #1019231f}.ol-preview-config__entry--inline:hover .ol-preview-config__part-action,.ol-preview-config__entry--inline:focus-within .ol-preview-config__part-action,.ol-preview-config__entry--stacked:hover .ol-preview-config__part-action,.ol-preview-config__entry--stacked:focus-within .ol-preview-config__part-action{opacity:1;pointer-events:auto;transform:translateY(0)scale(1)}.ol-preview-config__part-action:hover,.ol-preview-config__part-action:focus-visible,.ol-preview-config__part-action[aria-expanded=true]{border-color:var(--preview-ol-accent-current);color:var(--preview-ol-accent-current);box-shadow:0 0 0 3px var(--accent-halo);outline:none}.ol-preview-declare-part-popup{border:1px solid var(--preview-ol-border-current);background:var(--surface);z-index:7;z-index:60;border-radius:.9rem;gap:.35rem;min-width:min(16rem,100vw - 5rem);max-width:min(22rem,100vw - 1.5rem);max-height:min(22rem,100vh - 1.5rem);padding:.5rem;display:grid;position:fixed;overflow:auto;box-shadow:0 18px 32px #10192329}.ol-preview-config-key-popup{grid-template-columns:repeat(auto-fit,minmax(2.5rem,1fr));gap:.3rem;width:min(13rem,100vw - 1.5rem);min-width:min(11.5rem,100vw - 1.5rem);padding:.45rem}.ol-preview-config-time-popup{grid-template-columns:repeat(auto-fit,minmax(3.25rem,1fr));gap:.3rem;width:min(14rem,100vw - 1.5rem);min-width:min(12rem,100vw - 1.5rem);padding:.45rem}.ol-preview-config-attachment-popup{gap:.6rem;width:min(24rem,100vw - 1.5rem);min-width:min(18rem,100vw - 1.5rem);padding:.65rem .7rem}.ol-preview-config-locale-popup{gap:.45rem;width:min(16rem,100vw - 1.5rem);min-width:min(13rem,100vw - 1.5rem);padding:.55rem .6rem}.ol-preview-config__locale-form{grid-template-rows:auto minmax(0,1fr);gap:.45rem;max-height:min(20rem,100vh - 3rem);display:grid}.ol-preview-config__locale-filter{box-sizing:border-box;border:1px solid var(--preview-ol-border-current);background:var(--surface);width:100%;color:var(--heading);font:inherit;border-radius:.72rem;padding:.45rem .6rem}.ol-preview-config__locale-filter::placeholder{color:var(--song-view-muted)}.ol-preview-config__locale-filter:focus-visible{border-color:var(--preview-ol-accent-current);box-shadow:0 0 0 3px var(--accent-halo);outline:none}.ol-preview-config__locale-options{gap:.2rem;display:grid;overflow-y:auto}.ol-preview-config__declare-part-option--locale{font-variant-numeric:tabular-nums;padding:.4rem .6rem}.ol-preview-config-add-popup{width:min(18rem,100vw - 1.5rem);min-width:min(14rem,100vw - 1.5rem)}.ol-preview-declare-part-popup[hidden]{display:none}.ol-preview-config__declare-part-option{width:100%;color:var(--heading);font:inherit;text-align:left;cursor:pointer;background:0 0;border:1px solid #0000;border-radius:.72rem;padding:.55rem .75rem;transition:background .16s,border-color .16s,color .16s;display:block}.ol-preview-config__declare-part-option--key{text-align:center;border-radius:999px;width:auto;padding:.45rem .35rem;font-weight:600}.ol-preview-config__declare-part-option--time{text-align:center;border-radius:999px;width:auto;padding:.45rem .4rem;font-weight:600}.ol-preview-config__declare-part-option--config{font-weight:600}.ol-preview-config__declare-part-option--key.is-selected,.ol-preview-config__declare-part-option--time.is-selected{border-color:var(--preview-ol-accent-current);background:var(--preview-ol-chip-bg);color:var(--preview-ol-accent-current)}.ol-preview-config__declare-part-option:hover,.ol-preview-config__declare-part-option:focus-visible{border-color:var(--preview-ol-chip-border);background:var(--preview-ol-chip-bg);color:var(--preview-ol-accent-current);outline:none}.ol-preview-config__declare-part-option:disabled{color:var(--song-view-muted);cursor:not-allowed;opacity:.68}.ol-preview-config__attachment-form{gap:.55rem;display:grid}.ol-preview-config__attachment-label{gap:.32rem;display:grid}.ol-preview-config__attachment-label-text{color:var(--heading);font-size:.82rem;font-weight:600}.ol-preview-config__attachment-input{box-sizing:border-box;border:1px solid var(--preview-ol-border-current);background:var(--surface);width:100%;color:var(--heading);font:inherit;border-radius:.72rem;padding:.55rem .7rem}.ol-preview-config__attachment-input::placeholder{color:var(--song-view-muted)}.ol-preview-config__attachment-input:focus-visible{border-color:var(--preview-ol-accent-current);box-shadow:0 0 0 3px var(--accent-halo);outline:none}.ol-preview-config__attachment-input[aria-invalid=true]{border-color:#dc2626}.ol-preview-config__attachment-help{color:var(--song-view-muted);margin:0;font-size:.78rem;line-height:1.35}.ol-preview-config__attachment-actions{justify-content:flex-end;display:flex}.ol-preview-config__attachment-submit{appearance:none;border:1px solid var(--preview-ol-chip-border);background:var(--surface);color:var(--preview-ol-accent-current);font:inherit;cursor:pointer;border-radius:999px;padding:.5rem .9rem;font-weight:600;transition:border-color .16s,color .16s,box-shadow .16s,transform .16s}.ol-preview-config__attachment-submit:hover,.ol-preview-config__attachment-submit:focus-visible{border-color:var(--preview-ol-accent-current);color:var(--preview-ol-accent-current);box-shadow:0 0 0 3px var(--accent-halo);outline:none}.ol-preview-config__attachment-submit:active{transform:scale(.98)}.ol-preview-config__attachment-submit:disabled{opacity:.58;cursor:not-allowed;box-shadow:none}.ol-preview-config__declare-part-empty{color:var(--song-view-muted);margin:0;padding:.4rem .25rem .1rem;font-size:.84rem}.ol-preview-config__entry--stacked .ol-preview-config__value{margin:.2rem 0 0 1rem}.ol-preview-config__value .ol-preview-chord{font-size:1em}.ol-preview-config__key--patterns,.ol-preview-config__value--patterns{align-self:start}.ol-song-view__structure{box-shadow:0 8px 18px #10192314}.ol-song-view__missing-note,.ol-song-view__empty{background:#ffffff57}:is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Config]{--preview-ol-border-current:#7c3aed;--preview-ol-accent-current:#7c3aed}:is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Intro]{--preview-ol-border-current:#c2410c;--preview-ol-accent-current:#c2410c}:is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Verse]{--preview-ol-border-current:#15803d;--preview-ol-accent-current:#15803d}:is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Note]{--preview-ol-border-current:#0f766e;--preview-ol-accent-current:#0f766e}:is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Pre-Chorus]{--preview-ol-border-current:#2563eb;--preview-ol-accent-current:#2563eb}:is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Chorus]{--preview-ol-border-current:#1d4ed8;--preview-ol-accent-current:#1d4ed8}:is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Post-Chorus]{--preview-ol-border-current:#4338ca;--preview-ol-accent-current:#4338ca}:is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Final-Chorus]{--preview-ol-border-current:#6d28d9;--preview-ol-accent-current:#6d28d9}:is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Refrain]{--preview-ol-border-current:#0891b2;--preview-ol-accent-current:#0891b2}:is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Bridge]{--preview-ol-border-current:#db2777;--preview-ol-accent-current:#db2777}:is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Tag]{--preview-ol-border-current:#65a30d;--preview-ol-accent-current:#65a30d}:is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Turnaround]{--preview-ol-border-current:#334155;--preview-ol-accent-current:#334155}:is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Outro]{--preview-ol-border-current:#475569;--preview-ol-accent-current:#475569}:is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Instrumental]{--preview-ol-border-current:#ea580c;--preview-ol-accent-current:#ea580c}:is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Interlude]{--preview-ol-border-current:#ca8a04;--preview-ol-accent-current:#ca8a04}:is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Breakdown]{--preview-ol-border-current:#dc2626;--preview-ol-accent-current:#dc2626}:is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Vamp]{--preview-ol-border-current:#be185d;--preview-ol-accent-current:#be185d}:is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Solo]{--preview-ol-border-current:#d97706;--preview-ol-accent-current:#d97706}.ol-preview-structure-step[data-ol-header=Config]{--preview-ol-step-border:#7c3aed59;--preview-ol-step-bg:#7c3aed1f;--preview-ol-step-text:#6d28d9}.ol-preview-structure-step[data-ol-header=Intro]{--preview-ol-step-border:#c2410c59;--preview-ol-step-bg:#c2410c1f;--preview-ol-step-text:#c2410c}.ol-preview-structure-step[data-ol-header=Verse]{--preview-ol-step-border:#15803d59;--preview-ol-step-bg:#15803d1f;--preview-ol-step-text:#15803d}.ol-preview-structure-step[data-ol-header=Note]{--preview-ol-step-border:#0f766e59;--preview-ol-step-bg:#0f766e1f;--preview-ol-step-text:#0f766e}.ol-preview-structure-step[data-ol-header=Pre-Chorus]{--preview-ol-step-border:#2563eb57;--preview-ol-step-bg:#2563eb1f;--preview-ol-step-text:#2563eb}.ol-preview-structure-step[data-ol-header=Chorus]{--preview-ol-step-border:#1d4ed857;--preview-ol-step-bg:#1d4ed81f;--preview-ol-step-text:#1d4ed8}.ol-preview-structure-step[data-ol-header=Post-Chorus]{--preview-ol-step-border:#4338ca57;--preview-ol-step-bg:#4338ca1f;--preview-ol-step-text:#4338ca}.ol-preview-structure-step[data-ol-header=Final-Chorus]{--preview-ol-step-border:#6d28d957;--preview-ol-step-bg:#6d28d91f;--preview-ol-step-text:#6d28d9}.ol-preview-structure-step[data-ol-header=Refrain]{--preview-ol-step-border:#0891b257;--preview-ol-step-bg:#0891b21f;--preview-ol-step-text:#0891b2}.ol-preview-structure-step[data-ol-header=Bridge]{--preview-ol-step-border:#db277759;--preview-ol-step-bg:#db27771f;--preview-ol-step-text:#db2777}.ol-preview-structure-step[data-ol-header=Tag]{--preview-ol-step-border:#65a30d5c;--preview-ol-step-bg:#65a30d24;--preview-ol-step-text:#4d7c0f}.ol-preview-structure-step[data-ol-header=Turnaround]{--preview-ol-step-border:#3341554d;--preview-ol-step-bg:#3341551f;--preview-ol-step-text:#334155}.ol-preview-structure-step[data-ol-header=Outro]{--preview-ol-step-border:#4755694d;--preview-ol-step-bg:#4755691f;--preview-ol-step-text:#475569}.ol-preview-structure-step[data-ol-header=Instrumental]{--preview-ol-step-border:#ea580c59;--preview-ol-step-bg:#ea580c1f;--preview-ol-step-text:#c2410c}.ol-preview-structure-step[data-ol-header=Interlude]{--preview-ol-step-border:#ca8a0459;--preview-ol-step-bg:#ca8a0421;--preview-ol-step-text:#a16207}.ol-preview-structure-step[data-ol-header=Breakdown]{--preview-ol-step-border:#dc262657;--preview-ol-step-bg:#dc26261f;--preview-ol-step-text:#b91c1c}.ol-preview-structure-step[data-ol-header=Vamp]{--preview-ol-step-border:#be185d57;--preview-ol-step-bg:#be185d1f;--preview-ol-step-text:#be185d}.ol-preview-structure-step[data-ol-header=Solo]{--preview-ol-step-border:#d9770659;--preview-ol-step-bg:#d977061f;--preview-ol-step-text:#b45309}:root[data-theme=dark] .ol-song-view__structure,[data-ol-theme=dark] .ol-song-view__structure{box-shadow:0 10px 22px #00000038}:root[data-theme=dark] .ol-song-view__missing-note,:root[data-theme=dark] .ol-song-view__empty,[data-ol-theme=dark] .ol-song-view__missing-note,[data-ol-theme=dark] .ol-song-view__empty{background:#080d1347}:root[data-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Config],[data-ol-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Config]{--preview-ol-border-current:#a78bfa;--preview-ol-accent-current:#c4b5fd}:root[data-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Intro],[data-ol-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Intro]{--preview-ol-border-current:#fb923c;--preview-ol-accent-current:#fdba74}:root[data-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Verse],[data-ol-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Verse]{--preview-ol-border-current:#4ade80;--preview-ol-accent-current:#86efac}:root[data-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Note],[data-ol-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Note]{--preview-ol-border-current:#2dd4bf;--preview-ol-accent-current:#5eead4}:root[data-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Pre-Chorus],[data-ol-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Pre-Chorus]{--preview-ol-border-current:#60a5fa;--preview-ol-accent-current:#93c5fd}:root[data-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Chorus],[data-ol-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Chorus]{--preview-ol-border-current:#3b82f6;--preview-ol-accent-current:#93c5fd}:root[data-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Post-Chorus],[data-ol-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Post-Chorus]{--preview-ol-border-current:#818cf8;--preview-ol-accent-current:#a5b4fc}:root[data-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Final-Chorus],[data-ol-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Final-Chorus]{--preview-ol-border-current:#a78bfa;--preview-ol-accent-current:#c4b5fd}:root[data-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Refrain],[data-ol-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Refrain]{--preview-ol-border-current:#22d3ee;--preview-ol-accent-current:#67e8f9}:root[data-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Bridge],[data-ol-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Bridge]{--preview-ol-border-current:#f472b6;--preview-ol-accent-current:#f9a8d4}:root[data-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Tag],[data-ol-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Tag]{--preview-ol-border-current:#a3e635;--preview-ol-accent-current:#bef264}:root[data-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Turnaround],[data-ol-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Turnaround]{--preview-ol-border-current:#cbd5e1;--preview-ol-accent-current:#e2e8f0}:root[data-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Outro],[data-ol-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Outro]{--preview-ol-border-current:#94a3b8;--preview-ol-accent-current:#cbd5e1}:root[data-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Instrumental],[data-ol-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Instrumental]{--preview-ol-border-current:#fb923c;--preview-ol-accent-current:#fdba74}:root[data-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Interlude],[data-ol-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Interlude]{--preview-ol-border-current:#facc15;--preview-ol-accent-current:#fde047}:root[data-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Breakdown],[data-ol-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Breakdown]{--preview-ol-border-current:#f87171;--preview-ol-accent-current:#fca5a5}:root[data-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Vamp],[data-ol-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Vamp]{--preview-ol-border-current:#f472b6;--preview-ol-accent-current:#f9a8d4}:root[data-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Solo],[data-ol-theme=dark] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Solo]{--preview-ol-border-current:#fbbf24;--preview-ol-accent-current:#fde68a}:root[data-theme=dark] .ol-preview-structure-step[data-ol-header=Config],[data-ol-theme=dark] .ol-preview-structure-step[data-ol-header=Config]{--preview-ol-step-border:#a78bfa73;--preview-ol-step-bg:#a78bfa24;--preview-ol-step-text:#ddd6fe}:root[data-theme=dark] .ol-preview-structure-step[data-ol-header=Intro],[data-ol-theme=dark] .ol-preview-structure-step[data-ol-header=Intro]{--preview-ol-step-border:#fb923c6b;--preview-ol-step-bg:#fb923c24;--preview-ol-step-text:#fdba74}:root[data-theme=dark] .ol-preview-structure-step[data-ol-header=Verse],[data-ol-theme=dark] .ol-preview-structure-step[data-ol-header=Verse]{--preview-ol-step-border:#4ade806b;--preview-ol-step-bg:#4ade8024;--preview-ol-step-text:#bbf7d0}:root[data-theme=dark] .ol-preview-structure-step[data-ol-header=Note],[data-ol-theme=dark] .ol-preview-structure-step[data-ol-header=Note]{--preview-ol-step-border:#2dd4bf6b;--preview-ol-step-bg:#2dd4bf24;--preview-ol-step-text:#99f6e4}:root[data-theme=dark] .ol-preview-structure-step[data-ol-header=Pre-Chorus],[data-ol-theme=dark] .ol-preview-structure-step[data-ol-header=Pre-Chorus]{--preview-ol-step-border:#60a5fa6b;--preview-ol-step-bg:#60a5fa24;--preview-ol-step-text:#bfdbfe}:root[data-theme=dark] .ol-preview-structure-step[data-ol-header=Chorus],[data-ol-theme=dark] .ol-preview-structure-step[data-ol-header=Chorus]{--preview-ol-step-border:#3b82f66b;--preview-ol-step-bg:#3b82f624;--preview-ol-step-text:#bfdbfe}:root[data-theme=dark] .ol-preview-structure-step[data-ol-header=Post-Chorus],[data-ol-theme=dark] .ol-preview-structure-step[data-ol-header=Post-Chorus]{--preview-ol-step-border:#818cf86b;--preview-ol-step-bg:#818cf824;--preview-ol-step-text:#c7d2fe}:root[data-theme=dark] .ol-preview-structure-step[data-ol-header=Final-Chorus],[data-ol-theme=dark] .ol-preview-structure-step[data-ol-header=Final-Chorus]{--preview-ol-step-border:#a78bfa6b;--preview-ol-step-bg:#a78bfa24;--preview-ol-step-text:#ddd6fe}:root[data-theme=dark] .ol-preview-structure-step[data-ol-header=Refrain],[data-ol-theme=dark] .ol-preview-structure-step[data-ol-header=Refrain]{--preview-ol-step-border:#22d3ee6b;--preview-ol-step-bg:#22d3ee24;--preview-ol-step-text:#a5f3fc}:root[data-theme=dark] .ol-preview-structure-step[data-ol-header=Bridge],[data-ol-theme=dark] .ol-preview-structure-step[data-ol-header=Bridge]{--preview-ol-step-border:#f472b66b;--preview-ol-step-bg:#f472b624;--preview-ol-step-text:#fbcfe8}:root[data-theme=dark] .ol-preview-structure-step[data-ol-header=Tag],[data-ol-theme=dark] .ol-preview-structure-step[data-ol-header=Tag]{--preview-ol-step-border:#a3e63570;--preview-ol-step-bg:#a3e63524;--preview-ol-step-text:#d9f99d}:root[data-theme=dark] .ol-preview-structure-step[data-ol-header=Turnaround],[data-ol-theme=dark] .ol-preview-structure-step[data-ol-header=Turnaround]{--preview-ol-step-border:#cbd5e15c;--preview-ol-step-bg:#cbd5e11f;--preview-ol-step-text:#f1f5f9}:root[data-theme=dark] .ol-preview-structure-step[data-ol-header=Outro],[data-ol-theme=dark] .ol-preview-structure-step[data-ol-header=Outro]{--preview-ol-step-border:#94a3b85c;--preview-ol-step-bg:#94a3b81f;--preview-ol-step-text:#e2e8f0}:root[data-theme=dark] .ol-preview-structure-step[data-ol-header=Instrumental],[data-ol-theme=dark] .ol-preview-structure-step[data-ol-header=Instrumental]{--preview-ol-step-border:#fb923c6b;--preview-ol-step-bg:#fb923c24;--preview-ol-step-text:#fdba74}:root[data-theme=dark] .ol-preview-structure-step[data-ol-header=Interlude],[data-ol-theme=dark] .ol-preview-structure-step[data-ol-header=Interlude]{--preview-ol-step-border:#facc156b;--preview-ol-step-bg:#facc1524;--preview-ol-step-text:#fde68a}:root[data-theme=dark] .ol-preview-structure-step[data-ol-header=Breakdown],[data-ol-theme=dark] .ol-preview-structure-step[data-ol-header=Breakdown]{--preview-ol-step-border:#f871716b;--preview-ol-step-bg:#f8717124;--preview-ol-step-text:#fecaca}:root[data-theme=dark] .ol-preview-structure-step[data-ol-header=Vamp],[data-ol-theme=dark] .ol-preview-structure-step[data-ol-header=Vamp]{--preview-ol-step-border:#f472b66b;--preview-ol-step-bg:#f472b624;--preview-ol-step-text:#fbcfe8}:root[data-theme=dark] .ol-preview-structure-step[data-ol-header=Solo],[data-ol-theme=dark] .ol-preview-structure-step[data-ol-header=Solo]{--preview-ol-step-border:#fbbf246b;--preview-ol-step-bg:#fbbf2424;--preview-ol-step-text:#fde68a}:root[data-theme=light-bs] .ol-song-view__structure,[data-ol-theme=light-bs] .ol-song-view__structure{box-shadow:0 .5rem 1rem #00000026}:root[data-theme=light-bs] .ol-song-view__missing-note,:root[data-theme=light-bs] .ol-song-view__empty,[data-ol-theme=light-bs] .ol-song-view__missing-note,[data-ol-theme=light-bs] .ol-song-view__empty{background:#f8f9fa}:root[data-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Config],[data-ol-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Config]{--preview-ol-border-current:#6f42c1;--preview-ol-accent-current:#6f42c1}:root[data-theme=light-bs] .ol-preview-structure-step[data-ol-header=Config],[data-ol-theme=light-bs] .ol-preview-structure-step[data-ol-header=Config]{--preview-ol-step-border:#6f42c159;--preview-ol-step-bg:#6f42c11f;--preview-ol-step-text:#6f42c1}:root[data-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Intro],[data-ol-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Intro]{--preview-ol-border-current:#ca6510;--preview-ol-accent-current:#ca6510}:root[data-theme=light-bs] .ol-preview-structure-step[data-ol-header=Intro],[data-ol-theme=light-bs] .ol-preview-structure-step[data-ol-header=Intro]{--preview-ol-step-border:#ca651059;--preview-ol-step-bg:#ca65101f;--preview-ol-step-text:#ca6510}:root[data-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Verse],[data-ol-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Verse]{--preview-ol-border-current:#198754;--preview-ol-accent-current:#198754}:root[data-theme=light-bs] .ol-preview-structure-step[data-ol-header=Verse],[data-ol-theme=light-bs] .ol-preview-structure-step[data-ol-header=Verse]{--preview-ol-step-border:#19875459;--preview-ol-step-bg:#1987541f;--preview-ol-step-text:#198754}:root[data-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Note],[data-ol-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Note]{--preview-ol-border-current:#20c997;--preview-ol-accent-current:#20c997}:root[data-theme=light-bs] .ol-preview-structure-step[data-ol-header=Note],[data-ol-theme=light-bs] .ol-preview-structure-step[data-ol-header=Note]{--preview-ol-step-border:#20c99759;--preview-ol-step-bg:#20c9971f;--preview-ol-step-text:#20c997}:root[data-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Pre-Chorus],[data-ol-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Pre-Chorus]{--preview-ol-border-current:#0d6efd;--preview-ol-accent-current:#0d6efd}:root[data-theme=light-bs] .ol-preview-structure-step[data-ol-header=Pre-Chorus],[data-ol-theme=light-bs] .ol-preview-structure-step[data-ol-header=Pre-Chorus]{--preview-ol-step-border:#0d6efd59;--preview-ol-step-bg:#0d6efd1f;--preview-ol-step-text:#0d6efd}:root[data-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Chorus],[data-ol-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Chorus]{--preview-ol-border-current:#0a58ca;--preview-ol-accent-current:#0a58ca}:root[data-theme=light-bs] .ol-preview-structure-step[data-ol-header=Chorus],[data-ol-theme=light-bs] .ol-preview-structure-step[data-ol-header=Chorus]{--preview-ol-step-border:#0a58ca59;--preview-ol-step-bg:#0a58ca1f;--preview-ol-step-text:#0a58ca}:root[data-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Post-Chorus],[data-ol-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Post-Chorus]{--preview-ol-border-current:#6610f2;--preview-ol-accent-current:#6610f2}:root[data-theme=light-bs] .ol-preview-structure-step[data-ol-header=Post-Chorus],[data-ol-theme=light-bs] .ol-preview-structure-step[data-ol-header=Post-Chorus]{--preview-ol-step-border:#6610f259;--preview-ol-step-bg:#6610f21f;--preview-ol-step-text:#6610f2}:root[data-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Final-Chorus],[data-ol-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Final-Chorus]{--preview-ol-border-current:#520dc2;--preview-ol-accent-current:#520dc2}:root[data-theme=light-bs] .ol-preview-structure-step[data-ol-header=Final-Chorus],[data-ol-theme=light-bs] .ol-preview-structure-step[data-ol-header=Final-Chorus]{--preview-ol-step-border:#520dc259;--preview-ol-step-bg:#520dc21f;--preview-ol-step-text:#520dc2}:root[data-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Refrain],[data-ol-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Refrain]{--preview-ol-border-current:#0aa2c0;--preview-ol-accent-current:#0aa2c0}:root[data-theme=light-bs] .ol-preview-structure-step[data-ol-header=Refrain],[data-ol-theme=light-bs] .ol-preview-structure-step[data-ol-header=Refrain]{--preview-ol-step-border:#0aa2c059;--preview-ol-step-bg:#0aa2c01f;--preview-ol-step-text:#0aa2c0}:root[data-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Bridge],[data-ol-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Bridge]{--preview-ol-border-current:#d63384;--preview-ol-accent-current:#d63384}:root[data-theme=light-bs] .ol-preview-structure-step[data-ol-header=Bridge],[data-ol-theme=light-bs] .ol-preview-structure-step[data-ol-header=Bridge]{--preview-ol-step-border:#d6338459;--preview-ol-step-bg:#d633841f;--preview-ol-step-text:#d63384}:root[data-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Tag],[data-ol-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Tag]{--preview-ol-border-current:#1aa179;--preview-ol-accent-current:#1aa179}:root[data-theme=light-bs] .ol-preview-structure-step[data-ol-header=Tag],[data-ol-theme=light-bs] .ol-preview-structure-step[data-ol-header=Tag]{--preview-ol-step-border:#1aa17959;--preview-ol-step-bg:#1aa1791f;--preview-ol-step-text:#1aa179}:root[data-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Turnaround],[data-ol-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Turnaround]{--preview-ol-border-current:#495057;--preview-ol-accent-current:#495057}:root[data-theme=light-bs] .ol-preview-structure-step[data-ol-header=Turnaround],[data-ol-theme=light-bs] .ol-preview-structure-step[data-ol-header=Turnaround]{--preview-ol-step-border:#49505759;--preview-ol-step-bg:#4950571f;--preview-ol-step-text:#495057}:root[data-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Outro],[data-ol-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Outro]{--preview-ol-border-current:#6c757d;--preview-ol-accent-current:#6c757d}:root[data-theme=light-bs] .ol-preview-structure-step[data-ol-header=Outro],[data-ol-theme=light-bs] .ol-preview-structure-step[data-ol-header=Outro]{--preview-ol-step-border:#6c757d59;--preview-ol-step-bg:#6c757d1f;--preview-ol-step-text:#6c757d}:root[data-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Instrumental],[data-ol-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Instrumental]{--preview-ol-border-current:#fd7e14;--preview-ol-accent-current:#fd7e14}:root[data-theme=light-bs] .ol-preview-structure-step[data-ol-header=Instrumental],[data-ol-theme=light-bs] .ol-preview-structure-step[data-ol-header=Instrumental]{--preview-ol-step-border:#fd7e1459;--preview-ol-step-bg:#fd7e141f;--preview-ol-step-text:#fd7e14}:root[data-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Interlude],[data-ol-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Interlude]{--preview-ol-border-current:#cc9a06;--preview-ol-accent-current:#cc9a06}:root[data-theme=light-bs] .ol-preview-structure-step[data-ol-header=Interlude],[data-ol-theme=light-bs] .ol-preview-structure-step[data-ol-header=Interlude]{--preview-ol-step-border:#cc9a0659;--preview-ol-step-bg:#cc9a061f;--preview-ol-step-text:#cc9a06}:root[data-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Breakdown],[data-ol-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Breakdown]{--preview-ol-border-current:#dc3545;--preview-ol-accent-current:#dc3545}:root[data-theme=light-bs] .ol-preview-structure-step[data-ol-header=Breakdown],[data-ol-theme=light-bs] .ol-preview-structure-step[data-ol-header=Breakdown]{--preview-ol-step-border:#dc354559;--preview-ol-step-bg:#dc35451f;--preview-ol-step-text:#dc3545}:root[data-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Vamp],[data-ol-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Vamp]{--preview-ol-border-current:#ab296a;--preview-ol-accent-current:#ab296a}:root[data-theme=light-bs] .ol-preview-structure-step[data-ol-header=Vamp],[data-ol-theme=light-bs] .ol-preview-structure-step[data-ol-header=Vamp]{--preview-ol-step-border:#ab296a59;--preview-ol-step-bg:#ab296a1f;--preview-ol-step-text:#ab296a}:root[data-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Solo],[data-ol-theme=light-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Solo]{--preview-ol-border-current:#997404;--preview-ol-accent-current:#997404}:root[data-theme=light-bs] .ol-preview-structure-step[data-ol-header=Solo],[data-ol-theme=light-bs] .ol-preview-structure-step[data-ol-header=Solo]{--preview-ol-step-border:#99740459;--preview-ol-step-bg:#9974041f;--preview-ol-step-text:#997404}:root[data-theme=dark-bs] .ol-song-view__structure,[data-ol-theme=dark-bs] .ol-song-view__structure{box-shadow:0 .5rem 1rem #00000080}:root[data-theme=dark-bs] .ol-song-view__missing-note,:root[data-theme=dark-bs] .ol-song-view__empty,[data-ol-theme=dark-bs] .ol-song-view__missing-note,[data-ol-theme=dark-bs] .ol-song-view__empty{background:#212529}:root[data-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Config],[data-ol-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Config]{--preview-ol-border-current:#a98eda;--preview-ol-accent-current:#a98eda}:root[data-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Config],[data-ol-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Config]{--preview-ol-step-border:#a98eda59;--preview-ol-step-bg:#a98eda1f;--preview-ol-step-text:#a98eda}:root[data-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Intro],[data-ol-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Intro]{--preview-ol-border-current:#feb272;--preview-ol-accent-current:#feb272}:root[data-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Intro],[data-ol-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Intro]{--preview-ol-step-border:#feb27259;--preview-ol-step-bg:#feb2721f;--preview-ol-step-text:#feb272}:root[data-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Verse],[data-ol-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Verse]{--preview-ol-border-current:#75b798;--preview-ol-accent-current:#75b798}:root[data-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Verse],[data-ol-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Verse]{--preview-ol-step-border:#75b79859;--preview-ol-step-bg:#75b7981f;--preview-ol-step-text:#75b798}:root[data-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Note],[data-ol-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Note]{--preview-ol-border-current:#63e6be;--preview-ol-accent-current:#63e6be}:root[data-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Note],[data-ol-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Note]{--preview-ol-step-border:#63e6be59;--preview-ol-step-bg:#63e6be1f;--preview-ol-step-text:#63e6be}:root[data-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Pre-Chorus],[data-ol-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Pre-Chorus]{--preview-ol-border-current:#6ea8fe;--preview-ol-accent-current:#6ea8fe}:root[data-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Pre-Chorus],[data-ol-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Pre-Chorus]{--preview-ol-step-border:#6ea8fe59;--preview-ol-step-bg:#6ea8fe1f;--preview-ol-step-text:#6ea8fe}:root[data-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Chorus],[data-ol-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Chorus]{--preview-ol-border-current:#3d8bfd;--preview-ol-accent-current:#3d8bfd}:root[data-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Chorus],[data-ol-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Chorus]{--preview-ol-step-border:#3d8bfd59;--preview-ol-step-bg:#3d8bfd1f;--preview-ol-step-text:#3d8bfd}:root[data-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Post-Chorus],[data-ol-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Post-Chorus]{--preview-ol-border-current:#a370f7;--preview-ol-accent-current:#a370f7}:root[data-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Post-Chorus],[data-ol-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Post-Chorus]{--preview-ol-step-border:#a370f759;--preview-ol-step-bg:#a370f71f;--preview-ol-step-text:#a370f7}:root[data-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Final-Chorus],[data-ol-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Final-Chorus]{--preview-ol-border-current:#c29ffa;--preview-ol-accent-current:#c29ffa}:root[data-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Final-Chorus],[data-ol-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Final-Chorus]{--preview-ol-step-border:#c29ffa59;--preview-ol-step-bg:#c29ffa1f;--preview-ol-step-text:#c29ffa}:root[data-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Refrain],[data-ol-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Refrain]{--preview-ol-border-current:#6edff6;--preview-ol-accent-current:#6edff6}:root[data-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Refrain],[data-ol-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Refrain]{--preview-ol-step-border:#6edff659;--preview-ol-step-bg:#6edff61f;--preview-ol-step-text:#6edff6}:root[data-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Bridge],[data-ol-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Bridge]{--preview-ol-border-current:#e685b5;--preview-ol-accent-current:#e685b5}:root[data-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Bridge],[data-ol-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Bridge]{--preview-ol-step-border:#e685b559;--preview-ol-step-bg:#e685b51f;--preview-ol-step-text:#e685b5}:root[data-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Tag],[data-ol-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Tag]{--preview-ol-border-current:#79dfc1;--preview-ol-accent-current:#79dfc1}:root[data-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Tag],[data-ol-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Tag]{--preview-ol-step-border:#79dfc159;--preview-ol-step-bg:#79dfc11f;--preview-ol-step-text:#79dfc1}:root[data-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Turnaround],[data-ol-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Turnaround]{--preview-ol-border-current:#ced4da;--preview-ol-accent-current:#ced4da}:root[data-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Turnaround],[data-ol-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Turnaround]{--preview-ol-step-border:#ced4da59;--preview-ol-step-bg:#ced4da1f;--preview-ol-step-text:#ced4da}:root[data-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Outro],[data-ol-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Outro]{--preview-ol-border-current:#adb5bd;--preview-ol-accent-current:#adb5bd}:root[data-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Outro],[data-ol-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Outro]{--preview-ol-step-border:#adb5bd59;--preview-ol-step-bg:#adb5bd1f;--preview-ol-step-text:#adb5bd}:root[data-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Instrumental],[data-ol-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Instrumental]{--preview-ol-border-current:#fd9843;--preview-ol-accent-current:#fd9843}:root[data-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Instrumental],[data-ol-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Instrumental]{--preview-ol-step-border:#fd984359;--preview-ol-step-bg:#fd98431f;--preview-ol-step-text:#fd9843}:root[data-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Interlude],[data-ol-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Interlude]{--preview-ol-border-current:#ffda6a;--preview-ol-accent-current:#ffda6a}:root[data-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Interlude],[data-ol-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Interlude]{--preview-ol-step-border:#ffda6a59;--preview-ol-step-bg:#ffda6a1f;--preview-ol-step-text:#ffda6a}:root[data-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Breakdown],[data-ol-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Breakdown]{--preview-ol-border-current:#ea868f;--preview-ol-accent-current:#ea868f}:root[data-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Breakdown],[data-ol-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Breakdown]{--preview-ol-step-border:#ea868f59;--preview-ol-step-bg:#ea868f1f;--preview-ol-step-text:#ea868f}:root[data-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Vamp],[data-ol-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Vamp]{--preview-ol-border-current:#de5c9d;--preview-ol-accent-current:#de5c9d}:root[data-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Vamp],[data-ol-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Vamp]{--preview-ol-step-border:#de5c9d59;--preview-ol-step-bg:#de5c9d1f;--preview-ol-step-text:#de5c9d}:root[data-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Solo],[data-ol-theme=dark-bs] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Solo]{--preview-ol-border-current:#ffcd39;--preview-ol-accent-current:#ffcd39}:root[data-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Solo],[data-ol-theme=dark-bs] .ol-preview-structure-step[data-ol-header=Solo]{--preview-ol-step-border:#ffcd3959;--preview-ol-step-bg:#ffcd391f;--preview-ol-step-text:#ffcd39}[data-ol-theme=light][data-ol-theme] .ol-song-view__structure{box-shadow:0 8px 18px #10192314}[data-ol-theme=light][data-ol-theme] .ol-song-view__missing-note,[data-ol-theme=light][data-ol-theme] .ol-song-view__empty{background:#ffffff57}[data-ol-theme=light][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Config]{--preview-ol-border-current:#7c3aed;--preview-ol-accent-current:#7c3aed}[data-ol-theme=light][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Intro]{--preview-ol-border-current:#c2410c;--preview-ol-accent-current:#c2410c}[data-ol-theme=light][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Verse]{--preview-ol-border-current:#15803d;--preview-ol-accent-current:#15803d}[data-ol-theme=light][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Note]{--preview-ol-border-current:#0f766e;--preview-ol-accent-current:#0f766e}[data-ol-theme=light][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Pre-Chorus]{--preview-ol-border-current:#2563eb;--preview-ol-accent-current:#2563eb}[data-ol-theme=light][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Chorus]{--preview-ol-border-current:#1d4ed8;--preview-ol-accent-current:#1d4ed8}[data-ol-theme=light][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Post-Chorus]{--preview-ol-border-current:#4338ca;--preview-ol-accent-current:#4338ca}[data-ol-theme=light][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Final-Chorus]{--preview-ol-border-current:#6d28d9;--preview-ol-accent-current:#6d28d9}[data-ol-theme=light][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Refrain]{--preview-ol-border-current:#0891b2;--preview-ol-accent-current:#0891b2}[data-ol-theme=light][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Bridge]{--preview-ol-border-current:#db2777;--preview-ol-accent-current:#db2777}[data-ol-theme=light][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Tag]{--preview-ol-border-current:#65a30d;--preview-ol-accent-current:#65a30d}[data-ol-theme=light][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Turnaround]{--preview-ol-border-current:#334155;--preview-ol-accent-current:#334155}[data-ol-theme=light][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Outro]{--preview-ol-border-current:#475569;--preview-ol-accent-current:#475569}[data-ol-theme=light][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Instrumental]{--preview-ol-border-current:#ea580c;--preview-ol-accent-current:#ea580c}[data-ol-theme=light][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Interlude]{--preview-ol-border-current:#ca8a04;--preview-ol-accent-current:#ca8a04}[data-ol-theme=light][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Breakdown]{--preview-ol-border-current:#dc2626;--preview-ol-accent-current:#dc2626}[data-ol-theme=light][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Vamp]{--preview-ol-border-current:#be185d;--preview-ol-accent-current:#be185d}[data-ol-theme=light][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Solo]{--preview-ol-border-current:#d97706;--preview-ol-accent-current:#d97706}[data-ol-theme=light][data-ol-theme] .ol-preview-structure-step[data-ol-header=Config]{--preview-ol-step-border:#7c3aed59;--preview-ol-step-bg:#7c3aed1f;--preview-ol-step-text:#6d28d9}[data-ol-theme=light][data-ol-theme] .ol-preview-structure-step[data-ol-header=Intro]{--preview-ol-step-border:#c2410c59;--preview-ol-step-bg:#c2410c1f;--preview-ol-step-text:#c2410c}[data-ol-theme=light][data-ol-theme] .ol-preview-structure-step[data-ol-header=Verse]{--preview-ol-step-border:#15803d59;--preview-ol-step-bg:#15803d1f;--preview-ol-step-text:#15803d}[data-ol-theme=light][data-ol-theme] .ol-preview-structure-step[data-ol-header=Note]{--preview-ol-step-border:#0f766e59;--preview-ol-step-bg:#0f766e1f;--preview-ol-step-text:#0f766e}[data-ol-theme=light][data-ol-theme] .ol-preview-structure-step[data-ol-header=Pre-Chorus]{--preview-ol-step-border:#2563eb57;--preview-ol-step-bg:#2563eb1f;--preview-ol-step-text:#2563eb}[data-ol-theme=light][data-ol-theme] .ol-preview-structure-step[data-ol-header=Chorus]{--preview-ol-step-border:#1d4ed857;--preview-ol-step-bg:#1d4ed81f;--preview-ol-step-text:#1d4ed8}[data-ol-theme=light][data-ol-theme] .ol-preview-structure-step[data-ol-header=Post-Chorus]{--preview-ol-step-border:#4338ca57;--preview-ol-step-bg:#4338ca1f;--preview-ol-step-text:#4338ca}[data-ol-theme=light][data-ol-theme] .ol-preview-structure-step[data-ol-header=Final-Chorus]{--preview-ol-step-border:#6d28d957;--preview-ol-step-bg:#6d28d91f;--preview-ol-step-text:#6d28d9}[data-ol-theme=light][data-ol-theme] .ol-preview-structure-step[data-ol-header=Refrain]{--preview-ol-step-border:#0891b257;--preview-ol-step-bg:#0891b21f;--preview-ol-step-text:#0891b2}[data-ol-theme=light][data-ol-theme] .ol-preview-structure-step[data-ol-header=Bridge]{--preview-ol-step-border:#db277759;--preview-ol-step-bg:#db27771f;--preview-ol-step-text:#db2777}[data-ol-theme=light][data-ol-theme] .ol-preview-structure-step[data-ol-header=Tag]{--preview-ol-step-border:#65a30d5c;--preview-ol-step-bg:#65a30d24;--preview-ol-step-text:#4d7c0f}[data-ol-theme=light][data-ol-theme] .ol-preview-structure-step[data-ol-header=Turnaround]{--preview-ol-step-border:#3341554d;--preview-ol-step-bg:#3341551f;--preview-ol-step-text:#334155}[data-ol-theme=light][data-ol-theme] .ol-preview-structure-step[data-ol-header=Outro]{--preview-ol-step-border:#4755694d;--preview-ol-step-bg:#4755691f;--preview-ol-step-text:#475569}[data-ol-theme=light][data-ol-theme] .ol-preview-structure-step[data-ol-header=Instrumental]{--preview-ol-step-border:#ea580c59;--preview-ol-step-bg:#ea580c1f;--preview-ol-step-text:#c2410c}[data-ol-theme=light][data-ol-theme] .ol-preview-structure-step[data-ol-header=Interlude]{--preview-ol-step-border:#ca8a0459;--preview-ol-step-bg:#ca8a0421;--preview-ol-step-text:#a16207}[data-ol-theme=light][data-ol-theme] .ol-preview-structure-step[data-ol-header=Breakdown]{--preview-ol-step-border:#dc262657;--preview-ol-step-bg:#dc26261f;--preview-ol-step-text:#b91c1c}[data-ol-theme=light][data-ol-theme] .ol-preview-structure-step[data-ol-header=Vamp]{--preview-ol-step-border:#be185d57;--preview-ol-step-bg:#be185d1f;--preview-ol-step-text:#be185d}[data-ol-theme=light][data-ol-theme] .ol-preview-structure-step[data-ol-header=Solo]{--preview-ol-step-border:#d9770659;--preview-ol-step-bg:#d977061f;--preview-ol-step-text:#b45309}[data-ol-theme=dark][data-ol-theme] .ol-song-view__structure{box-shadow:0 10px 22px #00000038}[data-ol-theme=dark][data-ol-theme] .ol-song-view__missing-note,[data-ol-theme=dark][data-ol-theme] .ol-song-view__empty{background:#080d1347}[data-ol-theme=dark][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Config]{--preview-ol-border-current:#a78bfa;--preview-ol-accent-current:#c4b5fd}[data-ol-theme=dark][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Intro]{--preview-ol-border-current:#fb923c;--preview-ol-accent-current:#fdba74}[data-ol-theme=dark][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Verse]{--preview-ol-border-current:#4ade80;--preview-ol-accent-current:#86efac}[data-ol-theme=dark][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Note]{--preview-ol-border-current:#2dd4bf;--preview-ol-accent-current:#5eead4}[data-ol-theme=dark][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Pre-Chorus]{--preview-ol-border-current:#60a5fa;--preview-ol-accent-current:#93c5fd}[data-ol-theme=dark][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Chorus]{--preview-ol-border-current:#3b82f6;--preview-ol-accent-current:#93c5fd}[data-ol-theme=dark][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Post-Chorus]{--preview-ol-border-current:#818cf8;--preview-ol-accent-current:#a5b4fc}[data-ol-theme=dark][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Final-Chorus]{--preview-ol-border-current:#a78bfa;--preview-ol-accent-current:#c4b5fd}[data-ol-theme=dark][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Refrain]{--preview-ol-border-current:#22d3ee;--preview-ol-accent-current:#67e8f9}[data-ol-theme=dark][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Bridge]{--preview-ol-border-current:#f472b6;--preview-ol-accent-current:#f9a8d4}[data-ol-theme=dark][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Tag]{--preview-ol-border-current:#a3e635;--preview-ol-accent-current:#bef264}[data-ol-theme=dark][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Turnaround]{--preview-ol-border-current:#cbd5e1;--preview-ol-accent-current:#e2e8f0}[data-ol-theme=dark][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Outro]{--preview-ol-border-current:#94a3b8;--preview-ol-accent-current:#cbd5e1}[data-ol-theme=dark][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Instrumental]{--preview-ol-border-current:#fb923c;--preview-ol-accent-current:#fdba74}[data-ol-theme=dark][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Interlude]{--preview-ol-border-current:#facc15;--preview-ol-accent-current:#fde047}[data-ol-theme=dark][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Breakdown]{--preview-ol-border-current:#f87171;--preview-ol-accent-current:#fca5a5}[data-ol-theme=dark][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Vamp]{--preview-ol-border-current:#f472b6;--preview-ol-accent-current:#f9a8d4}[data-ol-theme=dark][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Solo]{--preview-ol-border-current:#fbbf24;--preview-ol-accent-current:#fde68a}[data-ol-theme=dark][data-ol-theme] .ol-preview-structure-step[data-ol-header=Config]{--preview-ol-step-border:#a78bfa73;--preview-ol-step-bg:#a78bfa24;--preview-ol-step-text:#ddd6fe}[data-ol-theme=dark][data-ol-theme] .ol-preview-structure-step[data-ol-header=Intro]{--preview-ol-step-border:#fb923c6b;--preview-ol-step-bg:#fb923c24;--preview-ol-step-text:#fdba74}[data-ol-theme=dark][data-ol-theme] .ol-preview-structure-step[data-ol-header=Verse]{--preview-ol-step-border:#4ade806b;--preview-ol-step-bg:#4ade8024;--preview-ol-step-text:#bbf7d0}[data-ol-theme=dark][data-ol-theme] .ol-preview-structure-step[data-ol-header=Note]{--preview-ol-step-border:#2dd4bf6b;--preview-ol-step-bg:#2dd4bf24;--preview-ol-step-text:#99f6e4}[data-ol-theme=dark][data-ol-theme] .ol-preview-structure-step[data-ol-header=Pre-Chorus]{--preview-ol-step-border:#60a5fa6b;--preview-ol-step-bg:#60a5fa24;--preview-ol-step-text:#bfdbfe}[data-ol-theme=dark][data-ol-theme] .ol-preview-structure-step[data-ol-header=Chorus]{--preview-ol-step-border:#3b82f66b;--preview-ol-step-bg:#3b82f624;--preview-ol-step-text:#bfdbfe}[data-ol-theme=dark][data-ol-theme] .ol-preview-structure-step[data-ol-header=Post-Chorus]{--preview-ol-step-border:#818cf86b;--preview-ol-step-bg:#818cf824;--preview-ol-step-text:#c7d2fe}[data-ol-theme=dark][data-ol-theme] .ol-preview-structure-step[data-ol-header=Final-Chorus]{--preview-ol-step-border:#a78bfa6b;--preview-ol-step-bg:#a78bfa24;--preview-ol-step-text:#ddd6fe}[data-ol-theme=dark][data-ol-theme] .ol-preview-structure-step[data-ol-header=Refrain]{--preview-ol-step-border:#22d3ee6b;--preview-ol-step-bg:#22d3ee24;--preview-ol-step-text:#a5f3fc}[data-ol-theme=dark][data-ol-theme] .ol-preview-structure-step[data-ol-header=Bridge]{--preview-ol-step-border:#f472b66b;--preview-ol-step-bg:#f472b624;--preview-ol-step-text:#fbcfe8}[data-ol-theme=dark][data-ol-theme] .ol-preview-structure-step[data-ol-header=Tag]{--preview-ol-step-border:#a3e63570;--preview-ol-step-bg:#a3e63524;--preview-ol-step-text:#d9f99d}[data-ol-theme=dark][data-ol-theme] .ol-preview-structure-step[data-ol-header=Turnaround]{--preview-ol-step-border:#cbd5e15c;--preview-ol-step-bg:#cbd5e11f;--preview-ol-step-text:#f1f5f9}[data-ol-theme=dark][data-ol-theme] .ol-preview-structure-step[data-ol-header=Outro]{--preview-ol-step-border:#94a3b85c;--preview-ol-step-bg:#94a3b81f;--preview-ol-step-text:#e2e8f0}[data-ol-theme=dark][data-ol-theme] .ol-preview-structure-step[data-ol-header=Instrumental]{--preview-ol-step-border:#fb923c6b;--preview-ol-step-bg:#fb923c24;--preview-ol-step-text:#fdba74}[data-ol-theme=dark][data-ol-theme] .ol-preview-structure-step[data-ol-header=Interlude]{--preview-ol-step-border:#facc156b;--preview-ol-step-bg:#facc1524;--preview-ol-step-text:#fde68a}[data-ol-theme=dark][data-ol-theme] .ol-preview-structure-step[data-ol-header=Breakdown]{--preview-ol-step-border:#f871716b;--preview-ol-step-bg:#f8717124;--preview-ol-step-text:#fecaca}[data-ol-theme=dark][data-ol-theme] .ol-preview-structure-step[data-ol-header=Vamp]{--preview-ol-step-border:#f472b66b;--preview-ol-step-bg:#f472b624;--preview-ol-step-text:#fbcfe8}[data-ol-theme=dark][data-ol-theme] .ol-preview-structure-step[data-ol-header=Solo]{--preview-ol-step-border:#fbbf246b;--preview-ol-step-bg:#fbbf2424;--preview-ol-step-text:#fde68a}[data-ol-theme=light-bs][data-ol-theme] .ol-song-view__structure{box-shadow:0 .5rem 1rem #00000026}[data-ol-theme=light-bs][data-ol-theme] .ol-song-view__missing-note,[data-ol-theme=light-bs][data-ol-theme] .ol-song-view__empty{background:#f8f9fa}[data-ol-theme=light-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Config]{--preview-ol-border-current:#6f42c1;--preview-ol-accent-current:#6f42c1}[data-ol-theme=light-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Config]{--preview-ol-step-border:#6f42c159;--preview-ol-step-bg:#6f42c11f;--preview-ol-step-text:#6f42c1}[data-ol-theme=light-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Intro]{--preview-ol-border-current:#ca6510;--preview-ol-accent-current:#ca6510}[data-ol-theme=light-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Intro]{--preview-ol-step-border:#ca651059;--preview-ol-step-bg:#ca65101f;--preview-ol-step-text:#ca6510}[data-ol-theme=light-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Verse]{--preview-ol-border-current:#198754;--preview-ol-accent-current:#198754}[data-ol-theme=light-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Verse]{--preview-ol-step-border:#19875459;--preview-ol-step-bg:#1987541f;--preview-ol-step-text:#198754}[data-ol-theme=light-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Note]{--preview-ol-border-current:#20c997;--preview-ol-accent-current:#20c997}[data-ol-theme=light-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Note]{--preview-ol-step-border:#20c99759;--preview-ol-step-bg:#20c9971f;--preview-ol-step-text:#20c997}[data-ol-theme=light-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Pre-Chorus]{--preview-ol-border-current:#0d6efd;--preview-ol-accent-current:#0d6efd}[data-ol-theme=light-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Pre-Chorus]{--preview-ol-step-border:#0d6efd59;--preview-ol-step-bg:#0d6efd1f;--preview-ol-step-text:#0d6efd}[data-ol-theme=light-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Chorus]{--preview-ol-border-current:#0a58ca;--preview-ol-accent-current:#0a58ca}[data-ol-theme=light-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Chorus]{--preview-ol-step-border:#0a58ca59;--preview-ol-step-bg:#0a58ca1f;--preview-ol-step-text:#0a58ca}[data-ol-theme=light-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Post-Chorus]{--preview-ol-border-current:#6610f2;--preview-ol-accent-current:#6610f2}[data-ol-theme=light-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Post-Chorus]{--preview-ol-step-border:#6610f259;--preview-ol-step-bg:#6610f21f;--preview-ol-step-text:#6610f2}[data-ol-theme=light-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Final-Chorus]{--preview-ol-border-current:#520dc2;--preview-ol-accent-current:#520dc2}[data-ol-theme=light-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Final-Chorus]{--preview-ol-step-border:#520dc259;--preview-ol-step-bg:#520dc21f;--preview-ol-step-text:#520dc2}[data-ol-theme=light-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Refrain]{--preview-ol-border-current:#0aa2c0;--preview-ol-accent-current:#0aa2c0}[data-ol-theme=light-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Refrain]{--preview-ol-step-border:#0aa2c059;--preview-ol-step-bg:#0aa2c01f;--preview-ol-step-text:#0aa2c0}[data-ol-theme=light-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Bridge]{--preview-ol-border-current:#d63384;--preview-ol-accent-current:#d63384}[data-ol-theme=light-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Bridge]{--preview-ol-step-border:#d6338459;--preview-ol-step-bg:#d633841f;--preview-ol-step-text:#d63384}[data-ol-theme=light-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Tag]{--preview-ol-border-current:#1aa179;--preview-ol-accent-current:#1aa179}[data-ol-theme=light-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Tag]{--preview-ol-step-border:#1aa17959;--preview-ol-step-bg:#1aa1791f;--preview-ol-step-text:#1aa179}[data-ol-theme=light-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Turnaround]{--preview-ol-border-current:#495057;--preview-ol-accent-current:#495057}[data-ol-theme=light-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Turnaround]{--preview-ol-step-border:#49505759;--preview-ol-step-bg:#4950571f;--preview-ol-step-text:#495057}[data-ol-theme=light-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Outro]{--preview-ol-border-current:#6c757d;--preview-ol-accent-current:#6c757d}[data-ol-theme=light-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Outro]{--preview-ol-step-border:#6c757d59;--preview-ol-step-bg:#6c757d1f;--preview-ol-step-text:#6c757d}[data-ol-theme=light-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Instrumental]{--preview-ol-border-current:#fd7e14;--preview-ol-accent-current:#fd7e14}[data-ol-theme=light-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Instrumental]{--preview-ol-step-border:#fd7e1459;--preview-ol-step-bg:#fd7e141f;--preview-ol-step-text:#fd7e14}[data-ol-theme=light-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Interlude]{--preview-ol-border-current:#cc9a06;--preview-ol-accent-current:#cc9a06}[data-ol-theme=light-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Interlude]{--preview-ol-step-border:#cc9a0659;--preview-ol-step-bg:#cc9a061f;--preview-ol-step-text:#cc9a06}[data-ol-theme=light-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Breakdown]{--preview-ol-border-current:#dc3545;--preview-ol-accent-current:#dc3545}[data-ol-theme=light-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Breakdown]{--preview-ol-step-border:#dc354559;--preview-ol-step-bg:#dc35451f;--preview-ol-step-text:#dc3545}[data-ol-theme=light-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Vamp]{--preview-ol-border-current:#ab296a;--preview-ol-accent-current:#ab296a}[data-ol-theme=light-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Vamp]{--preview-ol-step-border:#ab296a59;--preview-ol-step-bg:#ab296a1f;--preview-ol-step-text:#ab296a}[data-ol-theme=light-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Solo]{--preview-ol-border-current:#997404;--preview-ol-accent-current:#997404}[data-ol-theme=light-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Solo]{--preview-ol-step-border:#99740459;--preview-ol-step-bg:#9974041f;--preview-ol-step-text:#997404}[data-ol-theme=dark-bs][data-ol-theme] .ol-song-view__structure{box-shadow:0 .5rem 1rem #00000080}[data-ol-theme=dark-bs][data-ol-theme] .ol-song-view__missing-note,[data-ol-theme=dark-bs][data-ol-theme] .ol-song-view__empty{background:#212529}[data-ol-theme=dark-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Config]{--preview-ol-border-current:#a98eda;--preview-ol-accent-current:#a98eda}[data-ol-theme=dark-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Config]{--preview-ol-step-border:#a98eda59;--preview-ol-step-bg:#a98eda1f;--preview-ol-step-text:#a98eda}[data-ol-theme=dark-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Intro]{--preview-ol-border-current:#feb272;--preview-ol-accent-current:#feb272}[data-ol-theme=dark-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Intro]{--preview-ol-step-border:#feb27259;--preview-ol-step-bg:#feb2721f;--preview-ol-step-text:#feb272}[data-ol-theme=dark-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Verse]{--preview-ol-border-current:#75b798;--preview-ol-accent-current:#75b798}[data-ol-theme=dark-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Verse]{--preview-ol-step-border:#75b79859;--preview-ol-step-bg:#75b7981f;--preview-ol-step-text:#75b798}[data-ol-theme=dark-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Note]{--preview-ol-border-current:#63e6be;--preview-ol-accent-current:#63e6be}[data-ol-theme=dark-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Note]{--preview-ol-step-border:#63e6be59;--preview-ol-step-bg:#63e6be1f;--preview-ol-step-text:#63e6be}[data-ol-theme=dark-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Pre-Chorus]{--preview-ol-border-current:#6ea8fe;--preview-ol-accent-current:#6ea8fe}[data-ol-theme=dark-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Pre-Chorus]{--preview-ol-step-border:#6ea8fe59;--preview-ol-step-bg:#6ea8fe1f;--preview-ol-step-text:#6ea8fe}[data-ol-theme=dark-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Chorus]{--preview-ol-border-current:#3d8bfd;--preview-ol-accent-current:#3d8bfd}[data-ol-theme=dark-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Chorus]{--preview-ol-step-border:#3d8bfd59;--preview-ol-step-bg:#3d8bfd1f;--preview-ol-step-text:#3d8bfd}[data-ol-theme=dark-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Post-Chorus]{--preview-ol-border-current:#a370f7;--preview-ol-accent-current:#a370f7}[data-ol-theme=dark-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Post-Chorus]{--preview-ol-step-border:#a370f759;--preview-ol-step-bg:#a370f71f;--preview-ol-step-text:#a370f7}[data-ol-theme=dark-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Final-Chorus]{--preview-ol-border-current:#c29ffa;--preview-ol-accent-current:#c29ffa}[data-ol-theme=dark-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Final-Chorus]{--preview-ol-step-border:#c29ffa59;--preview-ol-step-bg:#c29ffa1f;--preview-ol-step-text:#c29ffa}[data-ol-theme=dark-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Refrain]{--preview-ol-border-current:#6edff6;--preview-ol-accent-current:#6edff6}[data-ol-theme=dark-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Refrain]{--preview-ol-step-border:#6edff659;--preview-ol-step-bg:#6edff61f;--preview-ol-step-text:#6edff6}[data-ol-theme=dark-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Bridge]{--preview-ol-border-current:#e685b5;--preview-ol-accent-current:#e685b5}[data-ol-theme=dark-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Bridge]{--preview-ol-step-border:#e685b559;--preview-ol-step-bg:#e685b51f;--preview-ol-step-text:#e685b5}[data-ol-theme=dark-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Tag]{--preview-ol-border-current:#79dfc1;--preview-ol-accent-current:#79dfc1}[data-ol-theme=dark-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Tag]{--preview-ol-step-border:#79dfc159;--preview-ol-step-bg:#79dfc11f;--preview-ol-step-text:#79dfc1}[data-ol-theme=dark-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Turnaround]{--preview-ol-border-current:#ced4da;--preview-ol-accent-current:#ced4da}[data-ol-theme=dark-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Turnaround]{--preview-ol-step-border:#ced4da59;--preview-ol-step-bg:#ced4da1f;--preview-ol-step-text:#ced4da}[data-ol-theme=dark-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Outro]{--preview-ol-border-current:#adb5bd;--preview-ol-accent-current:#adb5bd}[data-ol-theme=dark-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Outro]{--preview-ol-step-border:#adb5bd59;--preview-ol-step-bg:#adb5bd1f;--preview-ol-step-text:#adb5bd}[data-ol-theme=dark-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Instrumental]{--preview-ol-border-current:#fd9843;--preview-ol-accent-current:#fd9843}[data-ol-theme=dark-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Instrumental]{--preview-ol-step-border:#fd984359;--preview-ol-step-bg:#fd98431f;--preview-ol-step-text:#fd9843}[data-ol-theme=dark-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Interlude]{--preview-ol-border-current:#ffda6a;--preview-ol-accent-current:#ffda6a}[data-ol-theme=dark-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Interlude]{--preview-ol-step-border:#ffda6a59;--preview-ol-step-bg:#ffda6a1f;--preview-ol-step-text:#ffda6a}[data-ol-theme=dark-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Breakdown]{--preview-ol-border-current:#ea868f;--preview-ol-accent-current:#ea868f}[data-ol-theme=dark-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Breakdown]{--preview-ol-step-border:#ea868f59;--preview-ol-step-bg:#ea868f1f;--preview-ol-step-text:#ea868f}[data-ol-theme=dark-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Vamp]{--preview-ol-border-current:#de5c9d;--preview-ol-accent-current:#de5c9d}[data-ol-theme=dark-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Vamp]{--preview-ol-step-border:#de5c9d59;--preview-ol-step-bg:#de5c9d1f;--preview-ol-step-text:#de5c9d}[data-ol-theme=dark-bs][data-ol-theme] :is(.ol-preview-fence,.ol-song-view__section)[data-ol-header=Solo]{--preview-ol-border-current:#ffcd39;--preview-ol-accent-current:#ffcd39}[data-ol-theme=dark-bs][data-ol-theme] .ol-preview-structure-step[data-ol-header=Solo]{--preview-ol-step-border:#ffcd3959;--preview-ol-step-bg:#ffcd391f;--preview-ol-step-text:#ffcd39}@media (width<=992px){.ol-lyric-panel [data-ol-ref=openLyricPreview]{flex:auto;min-height:0;padding:1rem}.ol-lyric-panel [data-ol-ref=openLyricPreview]>*{width:100%}.open-lyric-render-surface{padding:1rem}.ol-song-view__structures{flex-direction:column}.ol-song-view__structure,.ol-song-view__pattern-card{width:100%}}@media (width<=640px){.ol-lyric-panel [data-ol-ref=openLyricPreview],.open-lyric-render-surface{padding:.85rem}}";
//#endregion
//#region src/editor/components/internal/preview-styles.ts
/**
* The compiled Open Lyric preview stylesheet (the song view plus the
* `.ol-preview-*` fence cards) as a raw CSS string — exactly what
* {@link ensurePreviewStylesInjected} injects. Exposed so a host can inject it
* itself (paired with the `isSkipStyleInjection` option), e.g. into a shadow
* root or a scoped node.
*/
function getInjectablePreviewStyleCss() {
	return styles_default;
}
//#endregion
//#region src/editor/scripts/preview.ts
var OL_FENCE_BLOCK_RE = /^```ol:([^\r\n]*)[ \t]*\r?\n([\s\S]*?)^```[ \t]*$/gm;
function normalizeNewlines(value) {
	return String(value ?? "").replace(/\r\n?/g, "\n");
}
function renderFallbackMarkdown(markdown) {
	return escapeHtml$1(markdown).replace(/^### (.*)$/gm, "<h3>$1</h3>").replace(/^## (.*)$/gm, "<h2>$1</h2>").replace(/^# (.*)$/gm, "<h1>$1</h1>").replace(/\*\*(.*?)\*\*/g, "<strong>$1</strong>").replace(/_(.*?)_/g, "<em>$1</em>").replace(/\n/g, "<br>");
}
function getLineNumberAtOffset(text, offset) {
	if (offset <= 0) return 1;
	return text.slice(0, offset).split("\n").length;
}
function getLineNumberAtEndOffset(text, endOffset) {
	if (endOffset <= 0) return 1;
	return getLineNumberAtOffset(text, Math.max(0, endOffset - 1));
}
function getFirstContentColumn(line) {
	const firstContentIndex = String(line ?? "").search(/\S/);
	return firstContentIndex === -1 ? 1 : firstContentIndex + 1;
}
function getEditorDataAttributes(lineNumber, column = 1) {
	if (!lineNumber) return "";
	return ` data-editor-line="${escapeHtml$1(lineNumber)}" data-editor-column="${escapeHtml$1(column || 1)}"`;
}
function getFirstRenderableLineInfo(text) {
	const lines = normalizeNewlines(text).split("\n");
	for (let index = 0; index < lines.length; index += 1) {
		const line = lines[index];
		if (!line.trim()) continue;
		return {
			lineOffset: index,
			column: getFirstContentColumn(line)
		};
	}
	return {
		lineOffset: 0,
		column: 1
	};
}
function createPreviewSegments(markdown) {
	const normalizedMarkdown = normalizeNewlines(markdown);
	const segments = [];
	let lastOffset = 0;
	OL_FENCE_BLOCK_RE.lastIndex = 0;
	for (const match of normalizedMarkdown.matchAll(OL_FENCE_BLOCK_RE)) {
		const matchOffset = match.index || 0;
		if (matchOffset > lastOffset) {
			const markdownChunk = normalizedMarkdown.slice(lastOffset, matchOffset);
			segments.push({
				type: "markdown",
				raw: markdownChunk,
				markdown: markdownChunk,
				startLineNumber: getLineNumberAtOffset(normalizedMarkdown, lastOffset),
				endLineNumber: getLineNumberAtEndOffset(normalizedMarkdown, matchOffset)
			});
		}
		const rawFence = match[0] || "";
		segments.push({
			type: "olFence",
			raw: rawFence,
			info: (match[1] || "").trim(),
			body: match[2] || "",
			startLineNumber: getLineNumberAtOffset(normalizedMarkdown, matchOffset),
			endLineNumber: getLineNumberAtEndOffset(normalizedMarkdown, matchOffset + rawFence.length)
		});
		lastOffset = matchOffset + rawFence.length;
	}
	if (lastOffset < normalizedMarkdown.length) {
		const markdownChunk = normalizedMarkdown.slice(lastOffset);
		segments.push({
			type: "markdown",
			raw: markdownChunk,
			markdown: markdownChunk,
			startLineNumber: getLineNumberAtOffset(normalizedMarkdown, lastOffset),
			endLineNumber: getLineNumberAtEndOffset(normalizedMarkdown, normalizedMarkdown.length)
		});
	}
	return segments;
}
function renderMarkdownChunk(markdown, startLineNumber) {
	if (!markdown.trim()) return "";
	const normalizedMarkdown = normalizeNewlines(markdown);
	const tokens = marked.lexer(normalizedMarkdown, {
		gfm: true,
		breaks: true
	});
	let searchOffset = 0;
	return tokens.map((token) => {
		const tokenRaw = token.raw || "";
		const tokenOffset = normalizedMarkdown.indexOf(tokenRaw, searchOffset);
		const resolvedOffset = tokenOffset === -1 ? searchOffset : tokenOffset;
		const lineInfo = getFirstRenderableLineInfo(tokenRaw);
		const lineNumber = startLineNumber + getLineNumberAtOffset(normalizedMarkdown, resolvedOffset) - 1 + lineInfo.lineOffset;
		const column = lineInfo.column;
		if (tokenOffset !== -1) searchOffset = tokenOffset + tokenRaw.length;
		return `<div class="ol-preview-markdown-block"${getEditorDataAttributes(lineNumber, column)}>${marked.parser([token])}</div>`;
	}).join("");
}
function renderPreviewSegmentContent(segment, helpers = previewHelpers) {
	if (!segment || typeof segment !== "object") return "";
	if (segment.type === "olFence") {
		const sourceLocation = getPreviewSourceLocation(segment.body, segment.startLineNumber);
		return renderOpenLyricFenceHtml(segment.info, segment.body, sourceLocation, helpers);
	}
	return renderMarkdownChunk(segment.markdown, segment.startLineNumber);
}
function renderPreviewSegmentContainer(segment, helpers = previewHelpers) {
	const content = renderPreviewSegmentContent(segment, helpers);
	if (!content) return "";
	return [
		`<div class="ol-preview-segment" data-preview-segment-type="${escapeHtml$1(segment.type)}" data-preview-segment-start-line="${escapeHtml$1(segment.startLineNumber)}" data-preview-segment-end-line="${escapeHtml$1(segment.endLineNumber)}">`,
		content,
		"</div>"
	].join("");
}
function renderMarkdownWithMarked(markdown, context = {}) {
	const helpers = context.previewHelpers || previewHelpers;
	return createPreviewSegments(markdown).map((segment) => renderPreviewSegmentContainer(segment, helpers)).join("\n");
}
var previewParser = new OLParser({
	marked: renderMarkdownWithMarked,
	beforeMarked: normalizeNewlines,
	afterMarked: sanitizeHtml
});
function renderMarkdownPreview(markdown, options = {}) {
	try {
		const helperOptions = options && typeof options === "object" ? { ...options } : {};
		if (helperOptions.showEmptyDocumentStart && !String(markdown ?? "").trim()) return sanitizeHtml(renderOpenLyricEmptyDocumentHtml(createPreviewHelpers(helperOptions)));
		if (!Object.prototype.hasOwnProperty.call(helperOptions, "patternPreviewContext")) helperOptions.patternPreviewContext = createStrummingPatternPreviewContextFromMarkdown(markdown);
		return previewParser.parse(markdown, { context: { previewHelpers: createPreviewHelpers(helperOptions) } });
	} catch (error) {
		console.error("Failed to render markdown preview", error);
		return sanitizeHtml(renderFallbackMarkdown(String(markdown || "")));
	}
}
//#endregion
//#region src/plugins/OpenLyric/preview/controller/export-docx.ts
var DOCX_ORDERED_LIST_REFERENCE = "markdown-preview-ordered-list";
var DOCX_MAX_LIST_LEVEL = 8;
var DOCX_BLOCKQUOTE_BORDER_COLOR = "94A3B8";
var DOCX_CODE_BACKGROUND = "EEF2F6";
var DOCX_LINK_COLOR = "0563C1";
var DOCX_TABLE_BORDER_COLOR = "CBD5E1";
var DOCX_TABLE_HEADER_BACKGROUND = "E2E8F0";
var DOCX_DEFAULT_BODY_FONT = "Calibri";
var DOCX_DEFAULT_CODE_FONT = "Consolas";
var DOCX_INDENT_STEP_TWIP = 360;
var DOCX_BLOCK_TAG_NAMES = /* @__PURE__ */ new Set([
	"ADDRESS",
	"ARTICLE",
	"ASIDE",
	"BLOCKQUOTE",
	"DIV",
	"DL",
	"FIELDSET",
	"FIGCAPTION",
	"FIGURE",
	"FOOTER",
	"FORM",
	"H1",
	"H2",
	"H3",
	"H4",
	"H5",
	"H6",
	"HEADER",
	"HR",
	"MAIN",
	"NAV",
	"OL",
	"P",
	"PRE",
	"SECTION",
	"TABLE",
	"UL"
]);
function clampListLevel(level) {
	return Math.max(0, Math.min(DOCX_MAX_LIST_LEVEL, Number(level) || 0));
}
function createOrderedListLevels(docxModule) {
	return Array.from({ length: 9 }, (_value, level) => {
		const listLevel = clampListLevel(level);
		const numberingText = Array.from({ length: listLevel + 1 }, (_entry, index) => `%${index + 1}`).join(".");
		return {
			level: listLevel,
			format: docxModule.LevelFormat.DECIMAL,
			text: `${numberingText}.`,
			alignment: docxModule.AlignmentType.START,
			style: { paragraph: { indent: {
				left: 720 * (listLevel + 1),
				hanging: 260
			} } }
		};
	});
}
function normalizeDocxWhitespace(text, { preserveWhitespace = false } = {}) {
	const normalizedText = String(text ?? "").replace(/\r\n?/gu, "\n").replace(/\u00a0/gu, " ");
	if (preserveWhitespace) return normalizedText;
	return normalizedText.replace(/[\t\n\f\v ]+/gu, " ");
}
function getResolvedHref(href) {
	const value = String(href ?? "").trim();
	if (!value) return "";
	try {
		return new URL(value, document.baseURI).href;
	} catch (_error) {
		return value;
	}
}
function isWrapperElement(element) {
	if (!(element instanceof HTMLElement)) return false;
	return element.id === "preview" || element.classList.contains("ol-preview-segment") || element.classList.contains("ol-preview-markdown-block") || element.classList.contains("markdown-preview-print-surface") || element.classList.contains("open-lyric-render-surface");
}
function isBlockElement(element) {
	if (!(element instanceof HTMLElement)) return false;
	return DOCX_BLOCK_TAG_NAMES.has(element.tagName);
}
function hasRenderableText(text, { preserveWhitespace = false } = {}) {
	const normalizedText = normalizeDocxWhitespace(text, { preserveWhitespace });
	return preserveWhitespace ? normalizedText.length > 0 : normalizedText.trim().length > 0;
}
function mergeRunOptions(baseOptions = {}, nextOptions = {}) {
	return {
		...baseOptions,
		...nextOptions,
		...baseOptions.underline || nextOptions.underline ? { underline: {
			...typeof baseOptions.underline === "object" ? baseOptions.underline : {},
			...typeof nextOptions.underline === "object" ? nextOptions.underline : {}
		} } : {}
	};
}
function createTextRuns(docxModule, text, runOptions = {}, options = {}) {
	const preserveWhitespace = Boolean(options.preserveWhitespace);
	const normalizedText = normalizeDocxWhitespace(text, { preserveWhitespace });
	if (!hasRenderableText(normalizedText, { preserveWhitespace })) return [];
	if (!preserveWhitespace) return [new docxModule.TextRun({
		...runOptions,
		text: normalizedText
	})];
	return normalizedText.split("\n").map((line, index) => {
		const lineText = line.length > 0 ? line : " ";
		return new docxModule.TextRun({
			...runOptions,
			text: lineText,
			...index > 0 ? { break: 1 } : {}
		});
	});
}
function buildParagraphOptions(docxModule, context = {}, nextOptions = {}) {
	const indentLeft = Math.max(0, Number(context.indentLeftTwip) || 0);
	const paragraphOptions = {
		spacing: { after: 160 },
		...nextOptions
	};
	if (indentLeft > 0 || nextOptions.indent) paragraphOptions.indent = {
		...nextOptions.indent || {},
		left: indentLeft
	};
	if ((Number(context.quoteDepth) || 0) > 0) paragraphOptions.border = {
		...nextOptions.border || {},
		left: {
			color: DOCX_BLOCKQUOTE_BORDER_COLOR,
			size: 10,
			space: 8,
			style: docxModule.BorderStyle.SINGLE
		}
	};
	return paragraphOptions;
}
function createParagraphFromInlineNodes(docxModule, nodes, context = {}, paragraphOptions = {}) {
	const children = collectInlineChildren(docxModule, nodes, context);
	if (!children.length) {
		const fallbackText = normalizeDocxWhitespace(nodes.map((node) => node?.textContent ?? "").join(" ")).trim();
		if (!fallbackText) return null;
		children.push(new docxModule.TextRun(mergeRunOptions(context.defaultRunOptions, { text: fallbackText })));
	}
	return new docxModule.Paragraph({
		...buildParagraphOptions(docxModule, context, paragraphOptions),
		children
	});
}
function collectInlineChildren(docxModule, nodes, context = {}, runOptions = {}) {
	const children = [];
	Array.from(nodes || []).forEach((node) => {
		if (node?.nodeType === Node.TEXT_NODE) {
			children.push(...createTextRuns(docxModule, node.textContent, mergeRunOptions(context.defaultRunOptions, runOptions), { preserveWhitespace: Boolean(runOptions.font === context.codeFontFamily) }));
			return;
		}
		if (!(node instanceof HTMLElement)) return;
		switch (node.tagName) {
			case "BR":
				children.push(new docxModule.TextRun({
					text: "",
					break: 1
				}));
				return;
			case "STRONG":
			case "B":
				children.push(...collectInlineChildren(docxModule, node.childNodes, context, mergeRunOptions(runOptions, { bold: true })));
				return;
			case "EM":
			case "I":
				children.push(...collectInlineChildren(docxModule, node.childNodes, context, mergeRunOptions(runOptions, { italics: true })));
				return;
			case "S":
			case "DEL":
				children.push(...collectInlineChildren(docxModule, node.childNodes, context, mergeRunOptions(runOptions, { strike: true })));
				return;
			case "SUP":
				children.push(...collectInlineChildren(docxModule, node.childNodes, context, mergeRunOptions(runOptions, { superScript: true })));
				return;
			case "SUB":
				children.push(...collectInlineChildren(docxModule, node.childNodes, context, mergeRunOptions(runOptions, { subScript: true })));
				return;
			case "MARK":
				children.push(...collectInlineChildren(docxModule, node.childNodes, context, mergeRunOptions(runOptions, { highlight: "yellow" })));
				return;
			case "CODE":
				children.push(...createTextRuns(docxModule, node.textContent, mergeRunOptions(context.defaultRunOptions, {
					...runOptions,
					font: context.codeFontFamily,
					shading: {
						fill: DOCX_CODE_BACKGROUND,
						type: docxModule.ShadingType.CLEAR
					}
				}), { preserveWhitespace: true }));
				return;
			case "A": {
				const link = getResolvedHref(node.getAttribute("href"));
				const linkChildren = collectInlineChildren(docxModule, node.childNodes, context, mergeRunOptions(runOptions, {
					color: DOCX_LINK_COLOR,
					underline: { type: docxModule.UnderlineType.SINGLE }
				}));
				if (!linkChildren.length) {
					const linkText = String(node.textContent ?? "").trim() || link;
					linkChildren.push(new docxModule.TextRun({
						...mergeRunOptions(context.defaultRunOptions, {
							color: DOCX_LINK_COLOR,
							underline: { type: docxModule.UnderlineType.SINGLE }
						}),
						text: linkText
					}));
				}
				if (link) {
					children.push(new docxModule.ExternalHyperlink({
						link,
						children: linkChildren
					}));
					return;
				}
				children.push(...linkChildren);
				return;
			}
			case "IMG": {
				const imageAlt = String(node.getAttribute("alt") ?? "").trim();
				const imageSource = getResolvedHref(node.getAttribute("src"));
				const imageText = imageAlt || imageSource || "Image";
				if (imageSource) {
					children.push(new docxModule.ExternalHyperlink({
						link: imageSource,
						children: [new docxModule.TextRun({
							...mergeRunOptions(context.defaultRunOptions, {
								color: DOCX_LINK_COLOR,
								underline: { type: docxModule.UnderlineType.SINGLE }
							}),
							text: imageText
						})]
					}));
					return;
				}
				children.push(new docxModule.TextRun({
					...mergeRunOptions(context.defaultRunOptions, runOptions),
					text: imageText
				}));
				return;
			}
			default: children.push(...collectInlineChildren(docxModule, node.childNodes, context, runOptions));
		}
	});
	return children;
}
function convertListItemToBlocks(docxModule, listItemElement, context, options) {
	const blocks = [];
	const trailingIndentContext = {
		...context,
		indentLeftTwip: (Number(context.indentLeftTwip) || 0) + DOCX_INDENT_STEP_TWIP
	};
	let leadingNodes = [];
	let hasPrimaryParagraph = false;
	const flushPrimaryParagraph = () => {
		if (!leadingNodes.length) return;
		const paragraph = createParagraphFromInlineNodes(docxModule, leadingNodes, context, options.ordered ? {
			numbering: {
				reference: DOCX_ORDERED_LIST_REFERENCE,
				level: clampListLevel(options.level)
			},
			spacing: { after: 80 }
		} : {
			bullet: { level: clampListLevel(options.level) },
			spacing: { after: 80 }
		});
		if (paragraph) {
			blocks.push(paragraph);
			hasPrimaryParagraph = true;
		}
		leadingNodes = [];
	};
	Array.from(listItemElement.childNodes).forEach((childNode) => {
		if (childNode instanceof HTMLElement && childNode.tagName === "P") {
			if (!hasPrimaryParagraph) {
				leadingNodes = Array.from(childNode.childNodes);
				flushPrimaryParagraph();
			} else blocks.push(...convertElementToDocxBlocks(docxModule, childNode, trailingIndentContext));
			return;
		}
		if (childNode instanceof HTMLElement && (childNode.tagName === "UL" || childNode.tagName === "OL")) {
			flushPrimaryParagraph();
			blocks.push(...convertElementToDocxBlocks(docxModule, childNode, {
				...context,
				indentLeftTwip: Number(context.indentLeftTwip) || 0,
				quoteDepth: Number(context.quoteDepth) || 0
			}, options.level + 1));
			return;
		}
		if (childNode instanceof HTMLElement && isBlockElement(childNode)) {
			flushPrimaryParagraph();
			blocks.push(...convertElementToDocxBlocks(docxModule, childNode, trailingIndentContext));
			return;
		}
		leadingNodes.push(childNode);
	});
	flushPrimaryParagraph();
	if (!blocks.length) blocks.push(new docxModule.Paragraph(options.ordered ? { numbering: {
		reference: DOCX_ORDERED_LIST_REFERENCE,
		level: clampListLevel(options.level)
	} } : { bullet: { level: clampListLevel(options.level) } }));
	return blocks;
}
function createCodeBlockParagraph(docxModule, preElement, context = {}) {
	const children = createTextRuns(docxModule, String(preElement.textContent ?? "").replace(/\r\n?/gu, "\n").replace(/\n$/u, "") || " ", mergeRunOptions(context.defaultRunOptions, {
		font: context.codeFontFamily,
		shading: {
			fill: DOCX_CODE_BACKGROUND,
			type: docxModule.ShadingType.CLEAR
		}
	}), { preserveWhitespace: true });
	return new docxModule.Paragraph({
		...buildParagraphOptions(docxModule, context, {
			spacing: { after: 180 },
			shading: {
				fill: DOCX_CODE_BACKGROUND,
				type: docxModule.ShadingType.CLEAR
			},
			indent: { left: (Number(context.indentLeftTwip) || 0) + 240 }
		}),
		children
	});
}
function createTableCellChildren(docxModule, cellElement, context = {}) {
	const cellContext = cellElement.tagName === "TH" ? {
		...context,
		defaultRunOptions: mergeRunOptions(context.defaultRunOptions, { bold: true })
	} : context;
	const blocks = convertNodeListToDocxBlocks(docxModule, cellElement.childNodes, cellContext);
	if (blocks.length) return blocks;
	return [new docxModule.Paragraph("")];
}
function createTableBlock(docxModule, tableElement, context = {}) {
	const rows = [];
	tableElement.querySelectorAll("tr").forEach((rowElement) => {
		if (!(rowElement instanceof HTMLTableRowElement)) return;
		const cells = Array.from(rowElement.children).filter((cellElement) => cellElement instanceof HTMLTableCellElement || cellElement instanceof HTMLTableColElement).map((cellElement) => {
			return new docxModule.TableCell({
				shading: cellElement instanceof HTMLTableCellElement && cellElement.tagName === "TH" ? {
					fill: DOCX_TABLE_HEADER_BACKGROUND,
					type: docxModule.ShadingType.CLEAR
				} : void 0,
				children: cellElement instanceof HTMLTableCellElement ? createTableCellChildren(docxModule, cellElement, context) : [new docxModule.Paragraph("")]
			});
		});
		if (!cells.length) return;
		rows.push(new docxModule.TableRow({ children: cells }));
	});
	if (!rows.length) return [];
	return [new docxModule.Table({
		rows,
		width: {
			size: 100,
			type: docxModule.WidthType.PERCENTAGE
		},
		borders: {
			top: {
				color: DOCX_TABLE_BORDER_COLOR,
				size: 1,
				style: docxModule.BorderStyle.SINGLE
			},
			bottom: {
				color: DOCX_TABLE_BORDER_COLOR,
				size: 1,
				style: docxModule.BorderStyle.SINGLE
			},
			left: {
				color: DOCX_TABLE_BORDER_COLOR,
				size: 1,
				style: docxModule.BorderStyle.SINGLE
			},
			right: {
				color: DOCX_TABLE_BORDER_COLOR,
				size: 1,
				style: docxModule.BorderStyle.SINGLE
			},
			insideHorizontal: {
				color: DOCX_TABLE_BORDER_COLOR,
				size: 1,
				style: docxModule.BorderStyle.SINGLE
			},
			insideVertical: {
				color: DOCX_TABLE_BORDER_COLOR,
				size: 1,
				style: docxModule.BorderStyle.SINGLE
			}
		}
	})];
}
var DOCX_FENCE_SKIPPED_TAG_NAMES = /* @__PURE__ */ new Set([
	"DIALOG",
	"FORM",
	"INPUT",
	"OPTION",
	"SCRIPT",
	"SELECT",
	"STYLE",
	"SVG",
	"TEMPLATE",
	"TEXTAREA"
]);
var DOCX_FENCE_LINE_TAG_NAMES = /* @__PURE__ */ new Set([
	...DOCX_BLOCK_TAG_NAMES,
	"DD",
	"DETAILS",
	"DT",
	"LI",
	"SUMMARY",
	"TR"
]);
/**
* Not the song: classes CSS hides from the reader, and the live preview's
* in-place editing controls whose labels would otherwise read as text (the
* Structure steps' `-`/`+` repeat buttons, "Add Config").
*/
var DOCX_FENCE_HIDDEN_CLASS_NAMES = [
	"ol-preview-bar--hidden",
	"ol-preview-chord--hidden",
	"ol-preview-lyric-segment__chord--hidden",
	"ol-preview-add-section",
	"ol-preview-structure-repeat-controls",
	"ol-preview-config__add-button",
	"ol-preview-config__part-action",
	"ol-preview-config__text-edit",
	"ol-preview-config__locale-remove",
	"ol-preview-config__attachment-remove",
	"ol-preview-config__pattern-duplicate",
	"ol-preview-config__pattern-remove",
	"ol-preview-fence__rename",
	"ol-preview-fence__edit",
	"ol-preview-fence__delete"
];
/** The live preview's editing affordances: `…-action` / `…-actions` rows. */
var DOCX_FENCE_ACTION_CLASS_RE = /[_-]actions?$/u;
/** ASCII whitespace collapses as HTML does; a no-break space is kept. */
var DOCX_FENCE_COLLAPSIBLE_SPACE_RE = /[\t\n\f\r ]+/gu;
function isSkippedDocxFenceElement(element) {
	if (DOCX_FENCE_SKIPPED_TAG_NAMES.has(String(element.tagName).toUpperCase()) || element.hasAttribute("hidden")) return true;
	return Array.from(element.classList).some((className) => DOCX_FENCE_HIDDEN_CLASS_NAMES.includes(className) || DOCX_FENCE_ACTION_CLASS_RE.test(className));
}
function getCurrentDocxFenceLine(collector) {
	if (!collector.lines.length) collector.lines.push([]);
	return collector.lines[collector.lines.length - 1];
}
function breakDocxFenceLine(collector) {
	if (getCurrentDocxFenceLine(collector).length) collector.lines.push([]);
}
function pushDocxFenceText(collector, text, style = {}) {
	const line = getCurrentDocxFenceLine(collector);
	let value = String(text ?? "").replace(DOCX_FENCE_COLLAPSIBLE_SPACE_RE, " ");
	const previousText = line.length ? line[line.length - 1].text : "";
	if (value.startsWith(" ") && (!line.length || previousText.endsWith(" "))) value = value.slice(1);
	if (value) line.push({
		...style,
		text: value
	});
}
function getDocxFenceChordText(chordElement) {
	const labelElement = chordElement.querySelector(".ol-preview-chord__label");
	const label = String(labelElement ? labelElement.textContent : chordElement.textContent).replace(/^\[|\]$/gu, "").trim();
	if (!label) return "";
	return chordElement.classList.contains("ol-preview-chord--with-brackets") ? `[${label}]` : label;
}
function collectDocxFenceNodes(nodes, collector, style = {}) {
	Array.from(nodes || []).forEach((node) => {
		if (node?.nodeType === Node.TEXT_NODE) {
			const text = String(node.textContent ?? "");
			if (!text.trim() && /\n/u.test(text) && !/\u00a0/u.test(text)) return;
			pushDocxFenceText(collector, text, style);
			return;
		}
		if (node instanceof HTMLElement && !isSkippedDocxFenceElement(node)) collectDocxFenceElement(node, collector, style);
	});
}
function collectDocxFenceElement(element, collector, style = {}) {
	const { classList } = element;
	if (classList.contains("ol-preview-chord")) {
		pushDocxFenceText(collector, getDocxFenceChordText(element), {
			...style,
			bold: true
		});
		return;
	}
	if (element.hasAttribute("data-pattern-source")) {
		const heading = element.querySelector("h1, h2, h3, h4, h5, h6");
		const headingText = String(heading?.textContent ?? "").replace(DOCX_FENCE_COLLAPSIBLE_SPACE_RE, " ").trim();
		breakDocxFenceLine(collector);
		if (headingText) {
			pushDocxFenceText(collector, headingText, {
				...style,
				bold: true
			});
			pushDocxFenceText(collector, ": ", style);
		}
		pushDocxFenceText(collector, element.getAttribute("data-pattern-source"), {
			...style,
			code: true
		});
		breakDocxFenceLine(collector);
		return;
	}
	if (classList.contains("ol-preview-config__entry")) {
		const stacked = classList.contains("ol-preview-config__entry--stacked");
		const keyElement = element.querySelector(".ol-preview-config__key");
		const valueElement = element.querySelector(".ol-preview-config__value");
		breakDocxFenceLine(collector);
		if (keyElement) collectDocxFenceNodes(keyElement.childNodes, collector, {
			...style,
			bold: true
		});
		if (stacked) {
			breakDocxFenceLine(collector);
			if (valueElement) collectDocxFenceNodes(valueElement.childNodes, collector, style);
		} else if (valueElement) {
			const { inline } = collector;
			pushDocxFenceText(collector, " ", style);
			collector.inline = true;
			collectDocxFenceNodes(valueElement.childNodes, collector, style);
			collector.inline = inline;
		}
		breakDocxFenceLine(collector);
		return;
	}
	if (classList.contains("ol-preview-structure-arrow")) {
		pushDocxFenceText(collector, " → ", style);
		return;
	}
	if (classList.contains("ol-preview-config__locale-item") && element.previousElementSibling?.classList.contains("ol-preview-config__locale-item")) pushDocxFenceText(collector, ", ", style);
	const tagName = String(element.tagName).toUpperCase();
	if (tagName === "BR") {
		collector.lines.push([]);
		return;
	}
	const nextStyle = { ...style };
	if (tagName === "STRONG" || tagName === "B") nextStyle.bold = true;
	else if (tagName === "EM" || tagName === "I") nextStyle.italics = true;
	else if (tagName === "CODE") nextStyle.code = true;
	else if (tagName === "A") {
		const href = String(element.getAttribute("href") ?? "").trim();
		if (href && !href.startsWith("#")) nextStyle.link = getResolvedHref(href);
	}
	const startsLine = !collector.inline && (DOCX_FENCE_LINE_TAG_NAMES.has(tagName) || classList.contains("ol-preview-line"));
	if (startsLine) breakDocxFenceLine(collector);
	collectDocxFenceNodes(element.childNodes, collector, nextStyle);
	if (startsLine) breakDocxFenceLine(collector);
}
function createDocxFenceRuns(docxModule, runs, context) {
	const children = [];
	let pendingLink = "";
	let pendingLinkRuns = [];
	const flushLink = () => {
		if (pendingLinkRuns.length) children.push(new docxModule.ExternalHyperlink({
			link: pendingLink,
			children: pendingLinkRuns
		}));
		pendingLink = "";
		pendingLinkRuns = [];
	};
	runs.forEach((run) => {
		const runOptions = { text: run.text.replace(/ /gu, " ") };
		if (run.bold) runOptions.bold = true;
		if (run.italics) runOptions.italics = true;
		if (run.code && context.codeFontFamily) runOptions.font = context.codeFontFamily;
		if (run.link) {
			runOptions.color = DOCX_LINK_COLOR;
			runOptions.underline = { type: docxModule.UnderlineType.SINGLE };
		}
		const textRun = new docxModule.TextRun(mergeRunOptions(context.defaultRunOptions, runOptions));
		if (run.link) {
			if (run.link !== pendingLink) {
				flushLink();
				pendingLink = run.link;
			}
			pendingLinkRuns.push(textRun);
			return;
		}
		flushLink();
		children.push(textRun);
	});
	flushLink();
	return children;
}
function trimDocxFenceLine(runs) {
	const trimmed = runs.map((run) => ({ ...run }));
	while (trimmed.length) {
		const lastRun = trimmed[trimmed.length - 1];
		lastRun.text = lastRun.text.replace(/[\s ]+$/u, "");
		if (lastRun.text) break;
		trimmed.pop();
	}
	return trimmed;
}
function convertOlFenceToDocxBlocks(docxModule, segmentElement, context = {}) {
	const fenceElement = segmentElement.querySelector(".ol-preview-fence") || segmentElement;
	const summaryElement = Array.from(fenceElement.children).find((child) => String(child.tagName).toUpperCase() === "SUMMARY");
	const titleElement = summaryElement?.querySelector(".ol-preview-fence__title") || summaryElement;
	const bodyElement = fenceElement.querySelector(".ol-preview-fence__body") || fenceElement;
	const baseIndentTwip = Number(context.indentLeftTwip) || 0;
	const blocks = [];
	const titleText = String(titleElement?.textContent ?? "").replace(DOCX_FENCE_COLLAPSIBLE_SPACE_RE, " ").trim();
	if (titleText) blocks.push(new docxModule.Paragraph({
		...buildParagraphOptions(docxModule, context, {
			keepNext: true,
			spacing: {
				before: 200,
				after: 60
			}
		}),
		children: [new docxModule.TextRun(mergeRunOptions(context.defaultRunOptions, {
			text: titleText,
			bold: true
		}))]
	}));
	const collector = {
		lines: [],
		inline: false
	};
	collectDocxFenceNodes(bodyElement === fenceElement ? Array.from(fenceElement.childNodes).filter((node) => node !== summaryElement) : bodyElement.childNodes, collector);
	const lines = collector.lines.map((runs) => trimDocxFenceLine(runs)).filter((runs) => runs.some((run) => run.text.trim()));
	const bodyContext = {
		...context,
		indentLeftTwip: baseIndentTwip + DOCX_INDENT_STEP_TWIP
	};
	lines.forEach((runs, index) => {
		blocks.push(new docxModule.Paragraph({
			...buildParagraphOptions(docxModule, bodyContext, { spacing: { after: index === lines.length - 1 ? 160 : 40 } }),
			children: createDocxFenceRuns(docxModule, runs, bodyContext)
		}));
	});
	return blocks;
}
function convertElementToDocxBlocks(docxModule, element, context = {}, listLevel = 0) {
	if (!(element instanceof HTMLElement)) return [];
	if (element.classList.contains("ol-preview-segment")) {
		if (element.dataset.previewSegmentType === "olFence") return convertOlFenceToDocxBlocks(docxModule, element, context);
		return convertNodeListToDocxBlocks(docxModule, element.childNodes, context);
	}
	if (isWrapperElement(element)) return convertNodeListToDocxBlocks(docxModule, element.childNodes, context);
	switch (element.tagName) {
		case "H1":
		case "H2":
		case "H3":
		case "H4":
		case "H5":
		case "H6": {
			const headingLevel = {
				H1: docxModule.HeadingLevel.HEADING_1,
				H2: docxModule.HeadingLevel.HEADING_2,
				H3: docxModule.HeadingLevel.HEADING_3,
				H4: docxModule.HeadingLevel.HEADING_4,
				H5: docxModule.HeadingLevel.HEADING_5,
				H6: docxModule.HeadingLevel.HEADING_6
			}[element.tagName];
			const paragraph = createParagraphFromInlineNodes(docxModule, element.childNodes, context, {
				heading: headingLevel,
				spacing: {
					before: 220,
					after: 140
				}
			});
			return paragraph ? [paragraph] : [];
		}
		case "P": {
			const paragraph = createParagraphFromInlineNodes(docxModule, element.childNodes, context);
			return paragraph ? [paragraph] : [];
		}
		case "PRE": return [createCodeBlockParagraph(docxModule, element, context)];
		case "BLOCKQUOTE": return convertNodeListToDocxBlocks(docxModule, element.childNodes, {
			...context,
			indentLeftTwip: (Number(context.indentLeftTwip) || 0) + DOCX_INDENT_STEP_TWIP,
			quoteDepth: (Number(context.quoteDepth) || 0) + 1
		});
		case "UL":
		case "OL": return Array.from(element.children).filter((childElement) => childElement instanceof HTMLLIElement).flatMap((listItemElement) => {
			return convertListItemToBlocks(docxModule, listItemElement, context, {
				level: clampListLevel(listLevel),
				ordered: element.tagName === "OL"
			});
		});
		case "TABLE": return createTableBlock(docxModule, element, context);
		case "HR": return [new docxModule.Paragraph({
			...buildParagraphOptions(docxModule, context, { spacing: {
				before: 120,
				after: 160
			} }),
			thematicBreak: true
		})];
		default: {
			if (isBlockElement(element)) return convertNodeListToDocxBlocks(docxModule, element.childNodes, context);
			const paragraph = createParagraphFromInlineNodes(docxModule, [element], context);
			return paragraph ? [paragraph] : [];
		}
	}
}
function convertNodeListToDocxBlocks(docxModule, nodes, context = {}) {
	const blocks = [];
	Array.from(nodes || []).forEach((node) => {
		if (node?.nodeType === Node.TEXT_NODE) {
			if (!hasRenderableText(node.textContent)) return;
			const paragraph = createParagraphFromInlineNodes(docxModule, [node], context);
			if (paragraph) blocks.push(paragraph);
			return;
		}
		if (!(node instanceof HTMLElement)) return;
		blocks.push(...convertElementToDocxBlocks(docxModule, node, context));
	});
	return blocks;
}
/** The namespaces `docx` writes on `word/fontTable.xml`. */
var DOCX_FONT_TABLE_NAMESPACES = [
	"xmlns:mc=\"http://schemas.openxmlformats.org/markup-compatibility/2006\"",
	"xmlns:r=\"http://schemas.openxmlformats.org/officeDocument/2006/relationships\"",
	"xmlns:w=\"http://schemas.openxmlformats.org/wordprocessingml/2006/main\"",
	"xmlns:w14=\"http://schemas.microsoft.com/office/word/2010/wordml\"",
	"xmlns:w15=\"http://schemas.microsoft.com/office/word/2012/wordml\"",
	"xmlns:w16cex=\"http://schemas.microsoft.com/office/word/2018/wordml/cex\"",
	"xmlns:w16cid=\"http://schemas.microsoft.com/office/word/2016/wordml/cid\"",
	"xmlns:w16=\"http://schemas.microsoft.com/office/word/2018/wordml\"",
	"xmlns:w16sdtdh=\"http://schemas.microsoft.com/office/word/2020/wordml/sdtdatahash\"",
	"xmlns:w16se=\"http://schemas.microsoft.com/office/word/2015/wordml/symex\"",
	"mc:Ignorable=\"w14 w15 w16se w16cid w16 w16cex w16sdtdh\""
].join(" ");
function escapeDocxXmlAttribute(value) {
	return String(value ?? "").replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");
}
/**
* The files to pack over `docx`'s own for `documentFile` (`Packer.toBlob(…,
* undefined, overrides)`): `word/fontTable.xml` again, each embedded font's
* key (`w:fontKey`) in capitals, when the document carries fonts. `docx`
* writes the key in lower case, which the schema's GUID type does not allow,
* and LibreOffice then leaves the font unused (checked: the same file shows
* Battambang once its key is in capitals). The font file itself is
* obfuscated with that key whatever its case, so only the table changes.
*/
function getMarkdownPreviewDocxPackOverrides(documentFile) {
	const fonts = documentFile?.FontTable?.fontOptionsWithKey ?? [];
	if (!fonts.length) return [];
	return [{
		path: "word/fontTable.xml",
		data: `<?xml version="1.0" encoding="UTF-8" standalone="yes"?><w:fonts ${DOCX_FONT_TABLE_NAMESPACES}>${fonts.map((font, index) => `<w:font w:name="${escapeDocxXmlAttribute(font.name)}">` + (font.characterSet ? `<w:charset w:val="${escapeDocxXmlAttribute(font.characterSet)}"/>` : "") + `<w:family w:val="auto"/><w:pitch w:val="variable"/><w:sig w:usb0="E0002AFF" w:usb1="C000247B" w:usb2="00000009" w:usb3="00000000" w:csb0="000001FF" w:csb1="00000000"/><w:embedRegular r:id="rId${index + 1}" w:fontKey="{${String(font.fontKey).toUpperCase()}}"/></w:font>`).join("")}</w:fonts>`
	}];
}
/**
* Build the `docx` `Document` for a rendered Markdown preview — the Markdown
* preview's "Download DOCX" document, without the panel around it: the caller
* supplies the rendered preview root (any element whose children are the
* preview's blocks) and the fonts, so a host with no live preview — a Node
* process rendering through `renderMarkdownPreview` — builds the same file.
* `fonts` are carried in the file ({@link readMarkdownPreviewDocxFonts}).
*/
function createMarkdownPreviewDocxDocument(docxModule, previewRoot, { title = "markdown-preview", bodyFontFamily = DOCX_DEFAULT_BODY_FONT, codeFontFamily = DOCX_DEFAULT_CODE_FONT, fonts = [] } = {}) {
	const documentChildren = convertNodeListToDocxBlocks(docxModule, previewRoot?.childNodes || [], {
		bodyFontFamily,
		codeFontFamily,
		defaultRunOptions: { font: bodyFontFamily },
		indentLeftTwip: 0,
		quoteDepth: 0
	});
	return new docxModule.Document({
		creator: OPEN_LYRIC_EDITOR_INFO.name,
		lastModifiedBy: OPEN_LYRIC_EDITOR_INFO.name,
		title,
		...fonts.length ? { fonts } : {},
		subject: "Markdown preview export",
		keywords: "markdown,docx,open-lyric",
		numbering: { config: [{
			reference: DOCX_ORDERED_LIST_REFERENCE,
			levels: createOrderedListLevels(docxModule)
		}] },
		sections: [{
			properties: { page: { margin: {
				top: 900,
				right: 900,
				bottom: 900,
				left: 900
			} } },
			children: documentChildren.length ? documentChildren : [new docxModule.Paragraph("")]
		}]
	});
}
//#endregion
//#region src/plugins/OpenLyric/preview/controller/pptx/transitions.ts
var OPEN_LYRIC_POWERPOINT_DIRECTION_SETS = {
	side: [
		["u", "From bottom"],
		["d", "From top"],
		["l", "From right"],
		["r", "From left"]
	],
	leftRight: [["l", "From right"], ["r", "From left"]],
	eight: [
		["u", "From bottom"],
		["d", "From top"],
		["l", "From right"],
		["r", "From left"],
		["lu", "From bottom right"],
		["ru", "From bottom left"],
		["ld", "From top right"],
		["rd", "From top left"]
	],
	diagonal: [
		["lu", "From bottom right"],
		["ru", "From bottom left"],
		["ld", "From top right"],
		["rd", "From top left"]
	],
	orientation: [["horz", "Horizontal"], ["vert", "Vertical"]],
	inOut: [["in", "In"], ["out", "Out"]],
	split: [
		["vert-out", "Vertical out"],
		["vert-in", "Vertical in"],
		["horz-out", "Horizontal out"],
		["horz-in", "Horizontal in"]
	],
	center: [
		["center", "From center"],
		["lu", "From bottom right"],
		["ru", "From bottom left"],
		["ld", "From top right"],
		["rd", "From top left"]
	]
};
var preset = (prst) => ({
	tag: "p15:prstTrans",
	attributes: { prst }
});
var OPEN_LYRIC_POWERPOINT_TRANSITION_SPECS = [
	{
		id: "morph",
		label: "Morph",
		group: "subtle",
		tag: "p159:morph",
		attributes: { option: "byObject" },
		isInOpenWorship: true
	},
	{
		id: "fade",
		label: "Fade",
		group: "subtle",
		tag: "p:fade",
		isInOpenWorship: true
	},
	{
		id: "fadeThroughBlack",
		label: "Fade through black",
		group: "subtle",
		tag: "p:fade",
		attributes: { thruBlk: "1" },
		isInOpenWorship: true
	},
	{
		id: "push",
		label: "Push",
		group: "subtle",
		tag: "p:push",
		directions: "side",
		defaultDirection: "u",
		isInOpenWorship: true
	},
	{
		id: "wipe",
		label: "Wipe",
		group: "subtle",
		tag: "p:wipe",
		directions: "side",
		defaultDirection: "r",
		isInOpenWorship: true
	},
	{
		id: "split",
		label: "Split",
		group: "subtle",
		tag: "p:split",
		directions: "split",
		defaultDirection: "vert-out",
		isInOpenWorship: true
	},
	{
		id: "reveal",
		label: "Reveal",
		group: "subtle",
		tag: "p14:reveal",
		directions: "leftRight",
		defaultDirection: "l",
		isInOpenWorship: true
	},
	{
		id: "cut",
		label: "Cut",
		group: "subtle",
		tag: "p:cut",
		isInOpenWorship: true
	},
	{
		id: "randomBars",
		label: "Random bars",
		group: "subtle",
		tag: "p:randomBar",
		directions: "orientation",
		defaultDirection: "vert",
		isInOpenWorship: true
	},
	{
		id: "circle",
		label: "Circle",
		group: "subtle",
		tag: "p:circle",
		isInOpenWorship: true
	},
	{
		id: "diamond",
		label: "Diamond",
		group: "subtle",
		tag: "p:diamond"
	},
	{
		id: "plus",
		label: "Plus",
		group: "subtle",
		tag: "p:plus"
	},
	{
		id: "uncover",
		label: "Uncover",
		group: "subtle",
		tag: "p:pull",
		directions: "eight",
		defaultDirection: "l",
		isInOpenWorship: true
	},
	{
		id: "cover",
		label: "Cover",
		group: "subtle",
		tag: "p:cover",
		directions: "eight",
		defaultDirection: "l",
		isInOpenWorship: true
	},
	{
		id: "flash",
		label: "Flash",
		group: "subtle",
		tag: "p14:flash"
	},
	{
		id: "fallOver",
		label: "Fall over",
		group: "exciting",
		...preset("fallOver")
	},
	{
		id: "drape",
		label: "Drape",
		group: "exciting",
		...preset("drape")
	},
	{
		id: "curtains",
		label: "Curtains",
		group: "exciting",
		...preset("curtains"),
		isInOpenWorship: true
	},
	{
		id: "wind",
		label: "Wind",
		group: "exciting",
		...preset("wind")
	},
	{
		id: "prestige",
		label: "Prestige",
		group: "exciting",
		...preset("prestige")
	},
	{
		id: "fracture",
		label: "Fracture",
		group: "exciting",
		...preset("fracture")
	},
	{
		id: "crush",
		label: "Crush",
		group: "exciting",
		...preset("crush")
	},
	{
		id: "peelOff",
		label: "Peel off",
		group: "exciting",
		...preset("peelOff")
	},
	{
		id: "pageCurl",
		label: "Page curl",
		group: "exciting",
		...preset("pageCurlDouble")
	},
	{
		id: "airplane",
		label: "Airplane",
		group: "exciting",
		...preset("airplane")
	},
	{
		id: "origami",
		label: "Origami",
		group: "exciting",
		...preset("origami")
	},
	{
		id: "dissolve",
		label: "Dissolve",
		group: "exciting",
		tag: "p:dissolve"
	},
	{
		id: "checkerboard",
		label: "Checkerboard",
		group: "exciting",
		tag: "p:checker",
		directions: "orientation",
		defaultDirection: "horz"
	},
	{
		id: "blinds",
		label: "Blinds",
		group: "exciting",
		tag: "p:blinds",
		directions: "orientation",
		defaultDirection: "horz"
	},
	{
		id: "clock",
		label: "Clock",
		group: "exciting",
		tag: "p:wheel",
		attributes: { spokes: "1" }
	},
	{
		id: "clockReverse",
		label: "Clock (counterclockwise)",
		group: "exciting",
		tag: "p14:wheelReverse",
		attributes: { spokes: "1" }
	},
	{
		id: "wedge",
		label: "Wedge",
		group: "exciting",
		tag: "p:wedge"
	},
	{
		id: "wheel",
		label: "Wheel",
		group: "exciting",
		tag: "p:wheel",
		attributes: { spokes: "4" }
	},
	{
		id: "ripple",
		label: "Ripple",
		group: "exciting",
		tag: "p14:ripple",
		directions: "center",
		defaultDirection: "center"
	},
	{
		id: "honeycomb",
		label: "Honeycomb",
		group: "exciting",
		tag: "p14:honeycomb"
	},
	{
		id: "glitter",
		label: "Glitter",
		group: "exciting",
		tag: "p14:glitter",
		directions: "side",
		defaultDirection: "l"
	},
	{
		id: "vortex",
		label: "Vortex",
		group: "exciting",
		tag: "p14:vortex",
		directions: "side",
		defaultDirection: "l"
	},
	{
		id: "shred",
		label: "Shred",
		group: "exciting",
		tag: "p14:shred",
		directions: "inOut",
		defaultDirection: "in"
	},
	{
		id: "switch",
		label: "Switch",
		group: "exciting",
		tag: "p14:switch",
		directions: "leftRight",
		defaultDirection: "r"
	},
	{
		id: "flip",
		label: "Flip",
		group: "exciting",
		tag: "p14:flip",
		directions: "leftRight",
		defaultDirection: "r"
	},
	{
		id: "gallery",
		label: "Gallery",
		group: "exciting",
		tag: "p14:gallery",
		directions: "leftRight",
		defaultDirection: "l"
	},
	{
		id: "cube",
		label: "Cube",
		group: "exciting",
		tag: "p14:prism",
		directions: "side",
		defaultDirection: "l"
	},
	{
		id: "doors",
		label: "Doors",
		group: "exciting",
		tag: "p14:doors",
		directions: "orientation",
		defaultDirection: "vert"
	},
	{
		id: "box",
		label: "Box",
		group: "exciting",
		tag: "p14:prism",
		attributes: { isInverted: "1" },
		directions: "side",
		defaultDirection: "l"
	},
	{
		id: "comb",
		label: "Comb",
		group: "exciting",
		tag: "p:comb",
		directions: "orientation",
		defaultDirection: "horz"
	},
	{
		id: "zoom",
		label: "Zoom",
		group: "exciting",
		tag: "p:zoom",
		directions: "inOut",
		defaultDirection: "in"
	},
	{
		id: "warp",
		label: "Warp",
		group: "exciting",
		tag: "p14:warp",
		directions: "inOut",
		defaultDirection: "in"
	},
	{
		id: "strips",
		label: "Strips",
		group: "exciting",
		tag: "p:strips",
		directions: "diagonal",
		defaultDirection: "lu"
	},
	{
		id: "newsflash",
		label: "Newsflash",
		group: "exciting",
		tag: "p:newsflash"
	},
	{
		id: "random",
		label: "Random",
		group: "exciting",
		tag: "p:random"
	},
	{
		id: "pan",
		label: "Pan",
		group: "dynamic",
		tag: "p14:pan",
		directions: "side",
		defaultDirection: "u"
	},
	{
		id: "ferrisWheel",
		label: "Ferris wheel",
		group: "dynamic",
		tag: "p14:ferris",
		directions: "leftRight",
		defaultDirection: "l"
	},
	{
		id: "conveyor",
		label: "Conveyor",
		group: "dynamic",
		tag: "p14:conveyor",
		directions: "leftRight",
		defaultDirection: "l"
	},
	{
		id: "rotate",
		label: "Rotate",
		group: "dynamic",
		tag: "p14:prism",
		attributes: { isContent: "1" },
		directions: "side",
		defaultDirection: "l"
	},
	{
		id: "window",
		label: "Window",
		group: "dynamic",
		tag: "p14:window",
		directions: "orientation",
		defaultDirection: "vert"
	},
	{
		id: "orbit",
		label: "Orbit",
		group: "dynamic",
		tag: "p14:prism",
		attributes: {
			isContent: "1",
			isInverted: "1"
		},
		directions: "side",
		defaultDirection: "l"
	},
	{
		id: "flyThrough",
		label: "Fly through",
		group: "dynamic",
		tag: "p14:flythrough",
		directions: "inOut",
		defaultDirection: "in"
	}
];
var SPECS_BY_ID = new Map(OPEN_LYRIC_POWERPOINT_TRANSITION_SPECS.map((spec) => [spec.id, spec]));
[...new Set(Object.values(OPEN_LYRIC_POWERPOINT_DIRECTION_SETS).flatMap((set) => set.map(([value]) => value)))];
function getOpenLyricPowerPointTransitionSpec(id) {
	return SPECS_BY_ID.get(String(id)) ?? null;
}
/** The `[value, label]` directions transition `id` takes; none for most. */
function listOpenLyricPowerPointTransitionDirections(id) {
	const spec = getOpenLyricPowerPointTransitionSpec(id);
	return spec?.directions ? OPEN_LYRIC_POWERPOINT_DIRECTION_SETS[spec.directions] : [];
}
/**
* `direction` if transition `id` takes it, else its own default; `''` for a
* transition with no direction.
*/
function resolveOpenLyricPowerPointTransitionDirection(id, direction) {
	const choices = listOpenLyricPowerPointTransitionDirections(id);
	if (!choices.length) return "";
	return choices.some(([value]) => value === direction) ? String(direction) : getOpenLyricPowerPointTransitionSpec(id)?.defaultDirection ?? choices[0][0];
}
/**
* How long a transition takes at each speed, in ms. The showier ones
* (everything outside the Subtle group) take half as long again, so a cube
* has time to turn.
*/
var TRANSITION_DURATION_MS = {
	slow: 2e3,
	med: 1e3,
	medium: 1e3,
	fast: 500
};
var SHOWY_TRANSITION_SCALE = 1.5;
/** How long transition `id` takes at `speed` (`med` and `medium` alike), in ms. */
function getOpenLyricPowerPointTransitionDurationMs(id, speed) {
	const base = TRANSITION_DURATION_MS[speed] ?? TRANSITION_DURATION_MS.med;
	const group = getOpenLyricPowerPointTransitionSpec(id)?.group ?? "subtle";
	return Math.round(base * (group === "subtle" ? 1 : SHOWY_TRANSITION_SCALE));
}
/** The directions each text effect takes, its default first; none for most. */
var OPEN_LYRIC_POWERPOINT_TEXT_EFFECT_DIRECTIONS = {
	fade: [],
	fly: [
		"u",
		"d",
		"l",
		"r",
		"lu",
		"ru",
		"ld",
		"rd"
	],
	wipe: [
		"r",
		"l",
		"u",
		"d"
	],
	split: [
		"vert-out",
		"vert-in",
		"horz-out",
		"horz-in"
	],
	circle: [],
	diamond: [],
	plus: [],
	randomBars: ["vert", "horz"],
	clock: [],
	wheel: [],
	wedge: [],
	dissolve: [],
	checkerboard: ["horz", "vert"],
	blinds: ["horz", "vert"],
	strips: [
		"lu",
		"ru",
		"ld",
		"rd"
	],
	zoom: []
};
Object.keys(OPEN_LYRIC_POWERPOINT_TEXT_EFFECT_DIRECTIONS);
/** Each text effect's name, as PowerPoint's Animation pane has it. */
var OPEN_LYRIC_POWERPOINT_TEXT_EFFECT_LABELS = {
	fade: "Fade",
	fly: "Fly in",
	wipe: "Wipe",
	split: "Split",
	circle: "Circle",
	diamond: "Diamond",
	plus: "Plus",
	randomBars: "Random bars",
	clock: "Clock",
	wheel: "Wheel",
	wedge: "Wedge",
	dissolve: "Dissolve",
	checkerboard: "Checkerboard",
	blinds: "Blinds",
	strips: "Strips",
	zoom: "Zoom"
};
/** `direction` if text effect `effect` takes it, else its default; `''` for one without. */
function resolveOpenLyricPowerPointTextDirection(effect, direction) {
	const choices = OPEN_LYRIC_POWERPOINT_TEXT_EFFECT_DIRECTIONS[effect] ?? [];
	if (!choices.length) return "";
	return choices.includes(String(direction)) ? String(direction) : choices[0];
}
//#endregion
//#region src/plugins/OpenLyric/preview/controller/pptx/transition-preview.ts
/**
* The engine. Its body is self-contained — it names nothing from outside it
* but the page's globals — because `String(createOpenLyricTransitionEngine)`
* is the copy the HTML export runs. Keep it so: no imports, no module-level
* names inside.
*/
function createOpenLyricTransitionEngine() {
	const clamp01 = (value) => Math.min(1, Math.max(0, value));
	const easeInOut = (t) => t < .5 ? 2 * t * t : 1 - (-2 * t + 2) ** 2 / 2;
	const easeIn = (t) => t * t;
	const easeOut = (t) => 1 - (1 - t) ** 2;
	const round = (value) => Math.round(value * 100) / 100;
	const percent = (fraction) => `${round(fraction * 100)}%`;
	const translate = (x, y) => `translate(${percent(x)}, ${percent(y)})`;
	const perspective = ({ width, height }) => `perspective(${round(Math.max(width, height) * 2)}px)`;
	/** Ends a slide half-way through a 3D turn, before its back would show. */
	const fadeNear = (progress, from) => clamp01((1 - progress) / (1 - from));
	/** A clip that shows nothing. */
	const NOTHING = "polygon(0 0, 0 0, 0 0)";
	const rect = (x, y, width, height) => width <= 0 || height <= 0 ? "" : `M${round(x)} ${round(y)}h${round(width)}v${round(height)}h${round(-width)}Z`;
	const polygonPath = (points) => points.length < 3 ? "" : `M${points.map(([x, y]) => `${round(x)} ${round(y)}`).join("L")}Z`;
	/** The union of `parts` (path data in stage pixels) as a clip. */
	const clipPaths = (parts) => {
		const data = parts.join("");
		return data ? `path('${data}')` : NOTHING;
	};
	/** A slice of a disc from `from` to `to` degrees (0 is 3 o'clock, clockwise). */
	function sector(cx, cy, radius, from, to) {
		if (to <= from) return "";
		const steps = Math.max(1, Math.ceil((to - from) / 10));
		const points = [[cx, cy]];
		for (let step = 0; step <= steps; step += 1) {
			const angle = (from + (to - from) * step / steps) * Math.PI / 180;
			points.push([cx + radius * Math.cos(angle), cy + radius * Math.sin(angle)]);
		}
		return polygonPath(points);
	}
	const regularPolygon = (cx, cy, radius, corners, startDegrees) => polygonPath(Array.from({ length: corners }, (_unused, index) => {
		const angle = (startDegrees + 360 * index / corners) * Math.PI / 180;
		return [cx + radius * Math.cos(angle), cy + radius * Math.sin(angle)];
	}));
	/**
	* How far along the slide's way a point lies (`fx`, `fy` as fractions of the
	* stage): 0 at the edge the transition starts from, 1 at the far one.
	*/
	function sweepPosition({ vector: [x, y] }, fx, fy) {
		const parts = [];
		if (x) parts.push(x > 0 ? fx : 1 - fx);
		if (y) parts.push(y > 0 ? fy : 1 - fy);
		return parts.length ? parts.reduce((sum, part) => sum + part, 0) / parts.length : Math.hypot(fx - .5, fy - .5) / Math.SQRT1_2;
	}
	/** The stage in square cells about `columns` across, revealed one by one. */
	function cellReveal(context, columns, draw) {
		const size = context.width / columns;
		const rows = Math.ceil(context.height / size);
		const parts = [];
		for (let row = 0; row < rows; row += 1) for (let column = 0; column < columns; column += 1) {
			const cx = (column + .5) * size;
			const cy = (row + .5) * size;
			parts.push(draw(cx, cy, size, row * columns + column, sweepPosition(context, cx / context.width, cy / context.height)));
		}
		return { in: { clipPath: clipPaths(parts) } };
	}
	/** The incoming slide uncovered by turning sweeps from the stage's centre. */
	function sweep({ width, height }, ranges) {
		const radius = Math.hypot(width, height);
		return { in: { clipPath: clipPaths(ranges.map(([from, to]) => sector(width / 2, height / 2, radius, from, to))) } };
	}
	/**
	* A turn of the slides on a prism: a cube seen from outside, or a box from
	* within (`isInverted`), about the axis the direction crosses.
	*/
	function prism(t, context, isInverted) {
		const [x, y] = context.vector;
		const e = easeInOut(t);
		const isHorizontal = x !== 0 || y === 0;
		const toward = isInverted ? -1 : 1;
		const depth = round((isHorizontal ? context.width : context.height) / 2);
		const face = (angle) => `${perspective(context)} translateZ(${-toward * depth}px) ${isHorizontal ? "rotateY" : "rotateX"}(${round(angle)}deg) translateZ(${toward * depth}px)`;
		const way = isHorizontal ? toward * (x || -1) : -toward * y;
		return {
			out: { transform: face(way * e * 90) },
			in: { transform: face(-way * (1 - e) * 90) }
		};
	}
	/**
	* The outgoing slide as two doors: swinging toward the viewer, or away
	* (`isSwingingIn`, Window), as the incoming one comes forward.
	*/
	function doors(t, context, isSwingingIn) {
		const e = easeInOut(t);
		const isSideBySide = context.direction !== "horz";
		const way = isSwingingIn ? -1 : 1;
		const door = (side) => isSideBySide ? {
			clipPath: side < 0 ? "inset(0 50% 0 0)" : "inset(0 0 0 50%)",
			transformOrigin: side < 0 ? "0% 50%" : "100% 50%",
			transform: `${perspective(context)} rotateY(${round(side * way * e * 100)}deg)`,
			opacity: fadeNear(e, .75)
		} : {
			clipPath: side < 0 ? "inset(0 0 50% 0)" : "inset(50% 0 0 0)",
			transformOrigin: side < 0 ? "50% 0%" : "50% 100%",
			transform: `${perspective(context)} rotateX(${round(-side * way * e * 100)}deg)`,
			opacity: fadeNear(e, .75)
		};
		return {
			isOutOnTop: true,
			outPieces: [door(-1), door(1)],
			in: {
				transform: `${perspective(context)} translateZ(${round(-(1 - e) * context.width * .4)}px)`,
				opacity: clamp01(t * 2)
			}
		};
	}
	/** Push: both slides move together, the old one out as the new one comes on. */
	const push = (t, { vector: [x, y] }) => {
		const e = easeInOut(t);
		return {
			in: { transform: translate(-x * (1 - e), -y * (1 - e)) },
			out: { transform: translate(x * e, y * e) }
		};
	};
	const EFFECTS = {
		morph: (t) => ({ in: { opacity: easeInOut(t) } }),
		fade: (t) => ({ in: { opacity: easeInOut(t) } }),
		fadeThroughBlack: (t) => ({
			in: { opacity: easeInOut(clamp01(t * 2 - 1)) },
			out: { opacity: easeInOut(clamp01(1 - t * 2)) }
		}),
		push,
		wipe: (t, { vector: [x, y] }) => {
			const hidden = percent(1 - easeInOut(t));
			return { in: { clipPath: `inset(${y < 0 ? hidden : 0} ${x > 0 ? hidden : 0} ${y > 0 ? hidden : 0} ${x < 0 ? hidden : 0})` } };
		},
		split: (t, { direction }) => {
			const e = easeInOut(t);
			const [orientation, way] = direction.split("-");
			const across = (amount) => orientation === "horz" ? `inset(${amount} 0 ${amount} 0)` : `inset(0 ${amount} 0 ${amount})`;
			return way === "in" ? {
				isOutOnTop: true,
				out: { clipPath: across(percent(e / 2)) }
			} : { in: { clipPath: across(percent((1 - e) / 2)) } };
		},
		reveal: (t, { vector: [x] }) => {
			const e = easeInOut(t);
			return {
				isOutOnTop: true,
				out: {
					transform: translate((x || -1) * e * .4, 0),
					opacity: clamp01(1 - t * 1.6)
				},
				in: {
					transform: translate(-(x || -1) * (1 - e) * .15, 0),
					opacity: clamp01((t - .35) / .65)
				}
			};
		},
		cut: () => ({}),
		randomBars: (t, { width, height, direction, random }) => {
			const count = 60;
			const parts = [];
			for (let index = 0; index < count; index += 1) if (random(index) < t) parts.push(direction === "vert" ? rect(index * width / count, 0, width / count + .5, height) : rect(0, index * height / count, width, height / count + .5));
			return { in: { clipPath: clipPaths(parts) } };
		},
		circle: (t, { width, height }) => ({ in: { clipPath: `circle(${round(easeInOut(t) * Math.hypot(width, height) / 2)}px at 50% 50%)` } }),
		diamond: (t) => {
			const reach = easeInOut(t) * 100;
			return { in: { clipPath: `polygon(50% ${round(50 - reach)}%, ${round(50 + reach)}% 50%, 50% ${round(50 + reach)}%, ${round(50 - reach)}% 50%)` } };
		},
		plus: (t) => {
			const e = easeInOut(t);
			const arm = e * 50;
			const reach = e * 100;
			return { in: { clipPath: `polygon(${[
				[50 - arm, 50 - reach],
				[50 + arm, 50 - reach],
				[50 + arm, 50 - arm],
				[50 + reach, 50 - arm],
				[50 + reach, 50 + arm],
				[50 + arm, 50 + arm],
				[50 + arm, 50 + reach],
				[50 - arm, 50 + reach],
				[50 - arm, 50 + arm],
				[50 - reach, 50 + arm],
				[50 - reach, 50 - arm],
				[50 - arm, 50 - arm]
			].map(([x, y]) => `${round(x)}% ${round(y)}%`).join(", ")})` } };
		},
		uncover: (t, { vector: [x, y] }) => {
			const e = easeInOut(t);
			return {
				isOutOnTop: true,
				out: { transform: translate(x * e, y * e) }
			};
		},
		cover: (t, { vector: [x, y] }) => {
			const e = easeInOut(t);
			return { in: { transform: translate(-x * (1 - e), -y * (1 - e)) } };
		},
		flash: (t) => ({
			in: { opacity: t < .5 ? 0 : 1 },
			overlay: {
				color: "#ffffff",
				opacity: t < .5 ? easeOut(t * 2) : 1 - easeIn((t - .5) * 2)
			}
		}),
		fallOver: (t, context) => {
			const e = easeIn(t);
			return {
				isOutOnTop: true,
				out: {
					transformOrigin: "50% 100%",
					transform: `${perspective(context)} rotateX(${round(e * 90)}deg)`,
					opacity: fadeNear(t, .8)
				}
			};
		},
		drape: (t, context) => {
			const e = easeIn(t);
			return {
				isOutOnTop: true,
				out: {
					transformOrigin: "50% 0%",
					transform: `${perspective(context)} translateY(${percent(e * 1.05)}) rotateX(${round(-e * 35)}deg) skewX(${round(Math.sin(t * Math.PI * 3) * 4 * (1 - t))}deg)`
				}
			};
		},
		curtains: (t) => {
			const e = easeInOut(t);
			const curtain = (side) => ({
				clipPath: side < 0 ? "inset(0 50% 0 0)" : "inset(0 0 0 50%)",
				transformOrigin: side < 0 ? "0% 50%" : "100% 50%",
				transform: `translateX(${percent(side * e * .55)}) scaleX(${round(1 - .5 * e)}) skewY(${round(side * Math.sin(e * Math.PI) * 3)}deg)`
			});
			return {
				isOutOnTop: true,
				outPieces: [curtain(-1), curtain(1)],
				in: { transform: `scale(${round(.94 + .06 * e)})` }
			};
		},
		wind: (t) => {
			const e = easeIn(t);
			return {
				isOutOnTop: true,
				out: {
					transformOrigin: "100% 50%",
					transform: `translateX(${percent(-e * 1.2)}) skewX(${round(e * 30)}deg) scaleY(${round(1 - .2 * e)})`,
					opacity: clamp01(1 - t * 1.2)
				},
				in: {
					transform: translate((1 - easeOut(t)) * .08, 0),
					opacity: easeOut(t)
				}
			};
		},
		prestige: (t, context) => {
			const e = easeInOut(t);
			return {
				isOutOnTop: true,
				out: {
					transformOrigin: "50% 100%",
					transform: `${perspective(context)} rotateX(${round(e * 75)}deg) scale(${round(1 - .25 * e)})`,
					opacity: clamp01(1 - t * 1.4)
				},
				in: {
					transform: `${perspective(context)} translateZ(${round(-(1 - e) * context.width * .3)}px)`,
					opacity: clamp01(t * 1.5)
				}
			};
		},
		fracture: (t, context) => {
			const columns = 4;
			const rows = 3;
			const pieces = [];
			for (let row = 0; row < rows; row += 1) for (let column = 0; column < columns; column += 1) {
				const index = row * columns + column;
				const p = easeIn(clamp01((t - context.random(index) * .35) / .65));
				const cx = (column + .5) / columns - .5;
				const cy = (row + .5) / rows - .5;
				const spin = (context.random(index + 50) - .5) * 2;
				pieces.push({
					clipPath: `inset(${percent(row / rows)} ${percent(1 - (column + 1) / columns)} ${percent(1 - (row + 1) / rows)} ${percent(column / columns)})`,
					transformOrigin: `${percent(cx + .5)} ${percent(cy + .5)}`,
					transform: `${perspective(context)} translate(${percent(cx * p * 1.6)}, ${percent(cy * p * 1.6 + .6 * p * p)}) rotateX(${round(spin * p * 120)}deg) rotateZ(${round(spin * p * 90)}deg)`,
					opacity: clamp01(1 - p * 1.2)
				});
			}
			return {
				isOutOnTop: true,
				outPieces: pieces,
				in: { transform: `scale(${round(.92 + .08 * easeOut(t))})` }
			};
		},
		crush: (t, context) => {
			const e = easeIn(t);
			return {
				isOutOnTop: true,
				out: {
					transform: `${perspective(context)} scale(${round(1 - .92 * e)}) rotateZ(${round(e * 40)}deg) rotateX(${round(e * 35)}deg) skewX(${round(e * 15)}deg)`,
					filter: `brightness(${round(1 - .4 * e)})`,
					opacity: fadeNear(t, .7)
				},
				in: { opacity: clamp01(t * 2) }
			};
		},
		peelOff: (t, context) => {
			const e = easeInOut(t);
			return {
				isOutOnTop: true,
				out: {
					transformOrigin: "0% 0%",
					transform: `${perspective(context)} rotate3d(${round(context.width)}, ${round(context.height)}, 0, ${round(-e * 110)}deg)`,
					filter: `brightness(${round(1 - .35 * e)})`,
					opacity: fadeNear(e, .7)
				}
			};
		},
		pageCurl: (t, context) => {
			const e = easeInOut(t);
			const page = (side) => ({
				clipPath: side < 0 ? "inset(0 50% 0 0)" : "inset(0 0 0 50%)",
				transformOrigin: side < 0 ? "0% 50%" : "100% 50%",
				transform: `${perspective(context)} rotateY(${round(side * e * 100)}deg)`,
				filter: `brightness(${round(1 - .5 * e)})`,
				opacity: fadeNear(e, .8)
			});
			return {
				isOutOnTop: true,
				outPieces: [page(-1), page(1)]
			};
		},
		airplane: (t, context) => {
			const fold = easeInOut(clamp01(t / .4));
			const fly = easeIn(clamp01((t - .3) / .7));
			return {
				isOutOnTop: true,
				out: {
					transform: `${perspective(context)} translate(${percent(fly * .9)}, ${percent(-fly * 1.1)}) rotateZ(${round(-fly * 25)}deg) rotateX(${round(fold * 50)}deg) scale(${round(1 - .55 * fold - .3 * fly)})`,
					opacity: fadeNear(t, .85)
				}
			};
		},
		origami: (t, context) => {
			const fold = easeInOut(clamp01(t / .6));
			const fly = easeIn(clamp01((t - .45) / .55));
			return {
				isOutOnTop: true,
				out: {
					transform: `${perspective(context)} translateY(${percent(-fly * 1.2)}) rotateY(${round(fold * 70)}deg) rotateZ(${round(fold * 20)}deg) scale(${round(1 - .6 * fold)})`,
					filter: `brightness(${round(1 - .3 * fold)})`,
					opacity: fadeNear(t, .85)
				}
			};
		},
		dissolve: (t, context) => cellReveal(context, 32, (cx, cy, size, index) => context.random(index) < t ? rect(cx - size / 2, cy - size / 2, size + .5, size + .5) : ""),
		checkerboard: (t, { width, height, direction }) => {
			const columns = 10;
			const rows = 6;
			const cellWidth = width / columns;
			const cellHeight = height / rows;
			const parts = [];
			for (let row = 0; row < rows; row += 1) for (let column = 0; column < columns; column += 1) if (direction === "vert") {
				const f = clamp01(t * 6.5 - row - column % 2 * .5);
				parts.push(rect(column * cellWidth, row * cellHeight, cellWidth + .5, f * cellHeight + (f > 0 ? .5 : 0)));
			} else {
				const f = clamp01(t * 10.5 - column - row % 2 * .5);
				parts.push(rect(column * cellWidth, row * cellHeight, f * cellWidth + (f > 0 ? .5 : 0), cellHeight + .5));
			}
			return { in: { clipPath: clipPaths(parts) } };
		},
		blinds: (t, { width, height, direction }) => {
			const count = 6;
			const e = easeInOut(t);
			return { in: { clipPath: clipPaths(Array.from({ length: count }, (_unused, index) => direction === "vert" ? rect(index * width / count, 0, e * width / count, height) : rect(0, index * height / count, width, e * height / count))) } };
		},
		clock: (t, context) => sweep(context, [[-90, -90 + easeInOut(t) * 360]]),
		clockReverse: (t, context) => sweep(context, [[-90 - easeInOut(t) * 360, -90]]),
		wedge: (t, context) => {
			const half = easeInOut(t) * 180;
			return sweep(context, [[-90 - half, -90 + half]]);
		},
		wheel: (t, context) => {
			const reach = easeInOut(t) * 90;
			return sweep(context, [
				0,
				1,
				2,
				3
			].map((spoke) => [-90 + spoke * 90, -90 + spoke * 90 + reach]));
		},
		ripple: (t, { width, height, direction, vector: [x, y] }) => {
			const [ox, oy] = direction === "center" ? [width / 2, height / 2] : [width * (.5 - .5 * x), height * (.5 - .5 * y)];
			const radius = Math.hypot(Math.max(ox, width - ox), Math.max(oy, height - oy));
			const e = easeInOut(t);
			const origin = `${round(ox)}px ${round(oy)}px`;
			return {
				in: {
					clipPath: `circle(${round(e * radius)}px at ${origin})`,
					transformOrigin: origin,
					transform: `scale(${round(1.08 - .08 * e)})`
				},
				out: {
					transformOrigin: origin,
					transform: `scale(${round(1 + .05 * e)})`
				}
			};
		},
		honeycomb: (t, { width, height, random }) => {
			const size = width / 12;
			const across = Math.sqrt(3) * size;
			const down = 1.5 * size;
			const parts = [];
			let index = 0;
			for (let row = 0; row * down <= height + size; row += 1) for (let column = 0; column * across <= width + across; column += 1) {
				const grow = easeOut(clamp01((t - random(index) * .6) / .4));
				index += 1;
				if (grow > 0) parts.push(regularPolygon(column * across + (row % 2 ? across / 2 : 0), row * down, size * 1.04 * grow, 6, -90));
			}
			return { in: { clipPath: clipPaths(parts) } };
		},
		glitter: (t, context) => cellReveal(context, 24, (cx, cy, size, index, position) => {
			const grow = clamp01((t - (position * .6 + context.random(index) * .25)) / .15);
			return grow > 0 ? regularPolygon(cx, cy, size * grow, 4, -90) : "";
		}),
		vortex: (t, context) => cellReveal(context, 16, (cx, cy, size, index, position) => {
			const grow = easeOut(clamp01((t - (position * .5 + context.random(index) * .35)) / .15));
			if (grow <= 0) return "";
			const half = size * (.5 + .25 * (1 - grow)) * grow + .5;
			const turn = (1 - grow) * Math.PI * 1.5;
			return polygonPath([
				[-half, -half],
				[half, -half],
				[half, half],
				[-half, half]
			].map(([x, y]) => [cx + x * Math.cos(turn) - y * Math.sin(turn), cy + x * Math.sin(turn) + y * Math.cos(turn)]));
		}),
		shred: (t, { width, height, direction }) => {
			const count = 24;
			const stripWidth = width / count;
			const e = easeInOut(t);
			const strips = (shown) => clipPaths(Array.from({ length: count }, (_unused, index) => rect(index * stripWidth, index % 2 ? height * (1 - shown) : 0, stripWidth + .5, height * shown)));
			return direction === "out" ? {
				isOutOnTop: true,
				out: { clipPath: strips(1 - e) }
			} : { in: { clipPath: strips(e) } };
		},
		switch: (t, context) => {
			const x = context.vector[0] || 1;
			const view = perspective(context);
			const place = (shift, turn, scale) => `${view} translateX(${percent(shift)}) rotateY(${round(turn)}deg) scale(${round(scale)})`;
			if (t < .5) {
				const s = easeInOut(t * 2);
				return {
					isOutOnTop: true,
					out: { transform: place(x * s * .55, -x * s * 35, 1 - .2 * s) },
					in: {
						transform: place(-x * s * .35, x * s * 35, .8),
						opacity: s
					}
				};
			}
			const s = easeInOut((t - .5) * 2);
			return {
				out: {
					transform: place(x * (1 - s) * .55, -x * (1 - s) * 35, .8),
					opacity: 1 - s
				},
				in: { transform: place(-x * (1 - s) * .35, x * (1 - s) * 35, .8 + .2 * s) }
			};
		},
		flip: (t, context) => {
			const x = context.vector[0] || 1;
			const lift = `${perspective(context)} scale(${round(1 - .15 * Math.sin(Math.PI * t))})`;
			return t < .5 ? {
				isOutOnTop: true,
				out: { transform: `${lift} rotateY(${round(x * easeIn(t * 2) * 90)}deg)` },
				in: { opacity: 0 }
			} : {
				out: { opacity: 0 },
				in: { transform: `${lift} rotateY(${round(-x * (1 - easeOut((t - .5) * 2)) * 90)}deg)` }
			};
		},
		gallery: (t, context) => {
			const x = context.vector[0] || -1;
			const e = easeInOut(t);
			const view = perspective(context);
			const dip = round(1 - .25 * Math.sin(Math.PI * e));
			return {
				out: { transform: `${view} translateX(${percent(x * e * 1.15)}) rotateY(${round(-x * e * 50)}deg) scale(${dip})` },
				in: { transform: `${view} translateX(${percent(-x * (1 - e) * 1.15)}) rotateY(${round(x * (1 - e) * 50)}deg) scale(${dip})` }
			};
		},
		cube: (t, context) => prism(t, context, false),
		doors: (t, context) => doors(t, context, false),
		box: (t, context) => prism(t, context, true),
		comb: (t, { direction }) => {
			const count = 8;
			const e = easeInOut(t);
			return { inPieces: Array.from({ length: count }, (_unused, index) => {
				const from = index % 2 ? 1 : -1;
				const start = percent(index / count);
				const end = percent(1 - (index + 1) / count);
				return direction === "vert" ? {
					clipPath: `inset(0 ${end} 0 ${start})`,
					transform: translate(0, from * (1 - e))
				} : {
					clipPath: `inset(${start} 0 ${end} 0)`,
					transform: translate(from * (1 - e), 0)
				};
			}) };
		},
		zoom: (t, { direction }) => {
			const e = easeInOut(t);
			return direction === "out" ? {
				in: {
					transform: `scale(${round(2.5 - 1.5 * e)})`,
					opacity: e
				},
				out: { transform: `scale(${round(1 - .3 * e)})` }
			} : {
				in: {
					transform: `scale(${round(.3 + .7 * e)})`,
					opacity: clamp01(e * 1.5)
				},
				out: {
					transform: `scale(${round(1 + .3 * e)})`,
					opacity: 1 - e
				}
			};
		},
		warp: (t, context) => {
			const e = easeInOut(t);
			const view = perspective(context);
			return context.direction === "out" ? {
				in: {
					transform: `${view} scale(${round(2 - e)}) rotateX(${round((1 - e) * 30)}deg) skewX(${round((1 - e) * 15)}deg)`,
					opacity: e
				},
				out: {
					transform: `scale(${round(1 - .2 * e)})`,
					opacity: 1 - e
				}
			} : {
				isOutOnTop: true,
				out: {
					transform: `${view} scale(${round(1 - .85 * e)}) rotateX(${round(e * 40)}deg) skewX(${round(e * 20)}deg)`,
					opacity: fadeNear(t, .6)
				},
				in: {
					transform: `scale(${round(1.15 - .15 * e)})`,
					opacity: clamp01(t * 1.5)
				}
			};
		},
		strips: (t, context) => cellReveal(context, 16, (cx, cy, size, _index, position) => t > position * .95 ? rect(cx - size / 2, cy - size / 2, size + .5, size + .5) : ""),
		newsflash: (t) => {
			const e = easeOut(t);
			return { in: { transform: `rotate(${round((1 - e) * 720)}deg) scale(${round(e)})` } };
		},
		pan: (t, context) => {
			const frame = push(t, context);
			const filter = `blur(${round(Math.sin(Math.PI * t) * 2)}px)`;
			return {
				in: {
					...frame.in,
					filter
				},
				out: {
					...frame.out,
					filter
				}
			};
		},
		ferrisWheel: (t, { vector: [x] }) => {
			const e = easeInOut(t);
			const way = x || -1;
			const origin = "50% 260%";
			return {
				out: {
					transformOrigin: origin,
					transform: `rotate(${round(way * e * 60)}deg)`
				},
				in: {
					transformOrigin: origin,
					transform: `rotate(${round(-way * (1 - e) * 60)}deg)`
				}
			};
		},
		conveyor: (t, context) => {
			const x = context.vector[0] || -1;
			const e = easeInOut(t);
			const view = perspective(context);
			const tilt = round(-x * 20 * Math.sin(Math.PI * e));
			const scale = round(1 - .15 * Math.sin(Math.PI * e));
			return {
				out: { transform: `${view} translateX(${percent(x * e)}) rotateY(${tilt}deg) scale(${scale})` },
				in: { transform: `${view} translateX(${percent(-x * (1 - e))}) rotateY(${tilt}deg) scale(${scale})` }
			};
		},
		rotate: (t, context) => prism(t, context, false),
		window: (t, context) => doors(t, context, true),
		orbit: (t, context) => {
			const frame = prism(t, context, true);
			return {
				out: {
					...frame.out,
					opacity: clamp01(1 - t * 1.2)
				},
				in: {
					...frame.in,
					opacity: clamp01(t * 1.5)
				}
			};
		},
		flyThrough: (t, { direction }) => {
			const e = easeInOut(t);
			return direction === "out" ? {
				in: {
					transform: `scale(${round(1.8 - .8 * e)})`,
					opacity: e
				},
				out: {
					transform: `scale(${round(1 - .5 * e)})`,
					opacity: 1 - e
				}
			} : {
				isOutOnTop: true,
				out: {
					transform: `scale(${round(1 + 1.5 * e)})`,
					opacity: clamp01(1 - e * 1.4)
				},
				in: {
					transform: `scale(${round(.5 + .5 * e)})`,
					opacity: e
				}
			};
		}
	};
	/**
	* The text effects: how one picture looks at each point of coming on
	* (0 to 1); leaving, the same from 1 back to 0. Each is the incoming half
	* of the transition PowerPoint's animation of that name looks like, where
	* that half is the whole of it.
	*/
	const TEXT_EFFECTS = {
		fade: (t, context) => EFFECTS.fade(t, context).in,
		fly: (t, context) => EFFECTS.cover(t, context).in,
		wipe: (t, context) => EFFECTS.wipe(t, context).in,
		split: (t, context) => {
			const [orientation, way] = context.direction.split("-");
			if (way !== "in") return EFFECTS.split(t, context).in;
			const reach = easeInOut(t) / 2;
			const { width, height } = context;
			return { clipPath: clipPaths(orientation === "horz" ? [rect(0, 0, width, height * reach), rect(0, height * (1 - reach), width, height * reach)] : [rect(0, 0, width * reach, height), rect(width * (1 - reach), 0, width * reach, height)]) };
		},
		circle: (t, context) => EFFECTS.circle(t, context).in,
		diamond: (t, context) => EFFECTS.diamond(t, context).in,
		plus: (t, context) => EFFECTS.plus(t, context).in,
		randomBars: (t, context) => EFFECTS.randomBars(t, context).in,
		clock: (t, context) => EFFECTS.clock(t, context).in,
		wheel: (t, context) => EFFECTS.wheel(t, context).in,
		wedge: (t, context) => EFFECTS.wedge(t, context).in,
		dissolve: (t, context) => EFFECTS.dissolve(t, context).in,
		checkerboard: (t, context) => EFFECTS.checkerboard(t, context).in,
		blinds: (t, context) => EFFECTS.blinds(t, context).in,
		strips: (t, context) => EFFECTS.strips(t, context).in,
		zoom: (t) => {
			const e = easeInOut(t);
			return {
				transform: `scale(${round(e)})`,
				opacity: e
			};
		}
	};
	/** Which way each direction moves the slides, y down. */
	const VECTORS = {
		u: [0, -1],
		d: [0, 1],
		l: [-1, 0],
		r: [1, 0],
		lu: [-1, -1],
		ru: [1, -1],
		ld: [-1, 1],
		rd: [1, 1]
	};
	/** What Random picks from: every transition that moves. */
	const RANDOM_CHOICES = Object.keys(EFFECTS).filter((id) => id !== "cut" && id !== "morph");
	/** The effect a transition plays: its own, or Fade for one without. */
	function getEffect(type) {
		return EFFECTS[type] ?? EFFECTS.fade;
	}
	/** Whether `type` has an effect of its own (Random picks one). */
	function hasEffect(type) {
		return type === "random" || Object.hasOwn(EFFECTS, type);
	}
	/** The context an effect plays in, in `direction` (resolved), on a `width` × `height` stage. */
	function createContext(direction, width, height, seed = 0) {
		return {
			width,
			height,
			direction,
			vector: VECTORS[direction] ?? [0, 0],
			random: (index) => {
				const value = Math.sin((index + 1) * 12.9898 + seed * 78.233) * 43758.5453;
				return value - Math.floor(value);
			}
		};
	}
	const now = () => globalThis.performance?.now() ?? Date.now();
	function requestFrame(callback) {
		if (typeof globalThis.requestAnimationFrame === "function") {
			const id = globalThis.requestAnimationFrame(callback);
			return () => globalThis.cancelAnimationFrame?.(id);
		}
		const id = globalThis.setTimeout(callback, 16);
		return () => globalThis.clearTimeout(id);
	}
	function applyLayerStyle(element, layer, zIndex) {
		const { style } = element;
		style.setProperty("transform", layer?.transform ?? "");
		style.setProperty("transform-origin", layer?.transformOrigin ?? "");
		style.setProperty("opacity", layer?.opacity === void 0 ? "" : String(round(clamp01(layer.opacity))));
		style.setProperty("clip-path", layer?.clipPath ?? "");
		style.setProperty("filter", layer?.filter ?? "");
		if (zIndex !== null) style.setProperty("z-index", String(zIndex));
	}
	function clearLayerStyle(element) {
		for (const property of [
			"transform",
			"transform-origin",
			"opacity",
			"clip-path",
			"filter",
			"z-index",
			"visibility"
		]) element.style.removeProperty(property);
	}
	function play(view, outgoing, incoming, { type: requested, direction, durationMs, random = Math.random, resolveDirection = (_type, chosen) => chosen ?? "", overlayClassName = "ol-pptx-dialog__stage-overlay" }) {
		const type = requested === "random" ? RANDOM_CHOICES[Math.floor(random() * RANDOM_CHOICES.length)] : requested;
		const extras = [];
		let cancelFrame = () => {};
		let isDone = false;
		let resolveFinished = () => {};
		const finished = new Promise((resolve) => {
			resolveFinished = resolve;
		});
		const finish = () => {
			if (isDone) return;
			isDone = true;
			cancelFrame();
			outgoing?.remove();
			for (const extra of extras) extra.remove();
			clearLayerStyle(incoming);
			resolveFinished();
		};
		if (!outgoing || type === "cut" || !(durationMs > 0)) {
			finish();
			return {
				type,
				finished,
				finish
			};
		}
		const effect = getEffect(type);
		const context = createContext(resolveDirection(type, direction), view.clientWidth || 1600, view.clientHeight || 900, random() * 1e3);
		const first = effect(0, context);
		const piecesOf = (layer, count) => Array.from({ length: count }, () => {
			const piece = layer.cloneNode(true);
			piece.setAttribute("aria-hidden", "true");
			layer.after(piece);
			extras.push(piece);
			return piece;
		});
		const inPieces = piecesOf(incoming, first.inPieces?.length ?? 0);
		const outPieces = piecesOf(outgoing, first.outPieces?.length ?? 0);
		let overlay = null;
		if (first.overlay) {
			overlay = view.ownerDocument.createElement("div");
			overlay.className = overlayClassName;
			overlay.style.background = first.overlay.color;
			view.append(overlay);
			extras.push(overlay);
		}
		const render = (t) => {
			const frame = effect(t, context);
			const outZ = frame.isOutOnTop ? 3 : 1;
			for (const [layer, pieces, style, pieceStyles, zIndex] of [[
				incoming,
				inPieces,
				frame.in,
				frame.inPieces,
				2
			], [
				outgoing,
				outPieces,
				frame.out,
				frame.outPieces,
				outZ
			]]) if (pieces.length) {
				layer.style.visibility = "hidden";
				pieces.forEach((piece, index) => applyLayerStyle(piece, pieceStyles?.[index], zIndex));
			} else applyLayerStyle(layer, style, zIndex);
			if (overlay) overlay.style.opacity = String(round(frame.overlay?.opacity ?? 0));
		};
		const start = now();
		render(0);
		const tick = () => {
			if (isDone) return;
			const t = clamp01((now() - start) / durationMs);
			render(t);
			if (t >= 1) finish();
			else cancelFrame = requestFrame(tick);
		};
		cancelFrame = requestFrame(tick);
		return {
			type,
			finished,
			finish
		};
	}
	function playBuild(view, { exits, entrances }, { random = Math.random } = {}) {
		const steps = [...exits.map((step) => ({
			step,
			isExit: true
		})), ...entrances.map((step) => ({
			step,
			isExit: false
		}))].map(({ step, isExit }) => ({
			isExit,
			element: step.element,
			durationMs: Math.max(0, Number(step.durationMs) || 0),
			look: TEXT_EFFECTS[step.effect] ?? TEXT_EFFECTS.fade,
			context: createContext(step.direction ?? "", step.element.offsetWidth || view.clientWidth || 1600, step.element.offsetHeight || view.clientHeight || 900, random() * 1e3)
		}));
		const lengthOf = (isExit) => Math.max(0, ...steps.filter((step) => step.isExit === isExit).map((step) => step.durationMs));
		const exitLength = lengthOf(true);
		const total = exitLength + lengthOf(false);
		const type = entrances[0]?.effect ?? exits[0]?.effect ?? "fade";
		let cancelFrame = () => {};
		let isDone = false;
		let resolveFinished = () => {};
		const finished = new Promise((resolve) => {
			resolveFinished = resolve;
		});
		const hide = (element) => {
			clearLayerStyle(element);
			element.style.visibility = "hidden";
		};
		const finish = () => {
			if (isDone) return;
			isDone = true;
			cancelFrame();
			for (const step of steps) if (step.isExit) hide(step.element);
			else clearLayerStyle(step.element);
			resolveFinished();
		};
		const render = (elapsed) => {
			for (const step of steps) if (step.isExit) if (elapsed >= step.durationMs) hide(step.element);
			else applyLayerStyle(step.element, step.look(1 - clamp01(elapsed / step.durationMs), step.context), null);
			else if (elapsed < exitLength) step.element.style.visibility = "hidden";
			else {
				step.element.style.removeProperty("visibility");
				applyLayerStyle(step.element, step.look(step.durationMs > 0 ? clamp01((elapsed - exitLength) / step.durationMs) : 1, step.context), null);
			}
		};
		if (!(total > 0)) {
			finish();
			return {
				type,
				finished,
				finish
			};
		}
		const start = now();
		render(0);
		const tick = () => {
			if (isDone) return;
			const elapsed = now() - start;
			render(elapsed);
			if (elapsed >= total) finish();
			else cancelFrame = requestFrame(tick);
		};
		cancelFrame = requestFrame(tick);
		return {
			type,
			finished,
			finish
		};
	}
	return {
		createContext,
		getEffect,
		hasEffect,
		play,
		playBuild
	};
}
createOpenLyricTransitionEngine();
//#endregion
//#region src/plugins/OpenLyric/preview/controller/pptx/html-slideshow-runtime.ts
/**
* Run the slideshow on the page it is in. `createEngine` is
* `createOpenLyricTransitionEngine` (`./transition-preview.ts`).
*/
function openLyricHtmlSlideshowRuntime(createEngine) {
	const root = document.documentElement;
	const $ = (id) => document.getElementById(id);
	const SVG_NS = "http://www.w3.org/2000/svg";
	const SEP = " · ";
	const ICONS = {
		first: "<path d=\"M6 5v14\"/><path d=\"M18 6l-8 6 8 6z\"/>",
		prev: "<path d=\"M15 5l-7 7 7 7\"/>",
		next: "<path d=\"M9 5l7 7-7 7\"/>",
		last: "<path d=\"M18 5v14\"/><path d=\"M6 6l8 6-8 6z\"/>",
		play: "<path d=\"M7 5l12 7-12 7z\"/>",
		replay: "<path d=\"M4 12a8 8 0 1 0 2.3-5.7\"/><path d=\"M4 4v4h4\"/>",
		theme: "<circle cx=\"12\" cy=\"12\" r=\"8\"/><path d=\"M12 4a8 8 0 0 1 0 16z\" fill=\"currentColor\"/>",
		gear: "<circle cx=\"12\" cy=\"12\" r=\"3\"/><path d=\"M19 12a7 7 0 0 0-.1-1.2l2-1.6-2-3.4-2.4 1a7 7 0 0 0-2-1.2L14 3h-4l-.5 2.6a7 7 0 0 0-2 1.2l-2.4-1-2 3.4 2 1.6a7 7 0 0 0 0 2.4l-2 1.6 2 3.4 2.4-1a7 7 0 0 0 2 1.2L10 21h4l.5-2.6a7 7 0 0 0 2-1.2l2.4 1 2-3.4-2-1.6A7 7 0 0 0 19 12z\"/>",
		help: "<circle cx=\"12\" cy=\"12\" r=\"9\"/><path d=\"M9.5 9.5a2.5 2.5 0 1 1 3.5 2.3c-.7.3-1 .9-1 1.6v.6\"/><path d=\"M12 17h.01\"/>",
		presenter: "<rect x=\"3\" y=\"4\" width=\"18\" height=\"12\" rx=\"1\"/><path d=\"M8 20h8\"/><path d=\"M12 16v4\"/>",
		close: "<path d=\"M6 6l12 12\"/><path d=\"M18 6L6 18\"/>",
		pause: "<path d=\"M9 5v14\"/><path d=\"M15 5v14\"/>",
		window: "<rect x=\"3\" y=\"5\" width=\"18\" height=\"14\" rx=\"1\"/><path d=\"M3 9h18\"/>",
		fullscreen: "<path d=\"M4 9V4h5\"/><path d=\"M20 9V4h-5\"/><path d=\"M4 15v5h5\"/><path d=\"M20 15v5h-5\"/>",
		clock: "<circle cx=\"12\" cy=\"13\" r=\"8\"/><path d=\"M12 9v4l2.5 2.5\"/><path d=\"M9 2h6\"/>"
	};
	function icon(name) {
		const svg = document.createElementNS(SVG_NS, "svg");
		svg.setAttribute("viewBox", "0 0 24 24");
		svg.setAttribute("aria-hidden", "true");
		svg.innerHTML = ICONS[name] ?? "";
		return svg;
	}
	function h(tag, attrs, children) {
		const element = document.createElement(tag);
		for (const [key, value] of Object.entries(attrs ?? {})) {
			if (value == null || value === false) continue;
			if (key === "class") element.className = String(value);
			else if (key === "text") element.textContent = String(value);
			else if (key.startsWith("on") && typeof value === "function") element.addEventListener(key.slice(2), value);
			else element.setAttribute(key, value === true ? "" : String(value));
		}
		for (const child of [].concat(children ?? [])) if (child) element.append(child);
		return element;
	}
	for (const element of document.querySelectorAll("[data-icon]")) element.prepend(icon(element.getAttribute("data-icon") ?? ""));
	let parsed = null;
	try {
		parsed = JSON.parse($("ol-deck")?.textContent ?? "null");
	} catch {
		parsed = null;
	}
	if (!parsed || typeof parsed !== "object" || !Array.isArray(parsed.slides)) {
		document.body.replaceChildren(h("div", { class: "fatal" }, [h("h1", { text: "This slide show cannot be read" }), h("p", { text: "The slides this page carries are missing or damaged. Export the presentation again." })]));
		return;
	}
	const deck = parsed;
	const strings = deck.strings && typeof deck.strings === "object" ? deck.strings : {};
	const t = (text, ...values) => (typeof strings[text] === "string" && strings[text] ? strings[text] : text).replace(/\{(\d)\}/gu, (placeholder, digit) => Number(digit) < values.length ? String(values[Number(digit)]) : placeholder);
	const W = deck.width > 0 ? deck.width : 1920;
	const H = deck.height > 0 ? deck.height : 1080;
	const slides = deck.slides;
	const media = Array.isArray(deck.media) ? deck.media : [];
	const directions = deck.directions && typeof deck.directions === "object" ? deck.directions : {};
	const deckName = deck.title || t("Slide show");
	const engine = createEngine();
	root.style.setProperty("--aspect", `${W} / ${H}`);
	document.title = deckName;
	const PREF_KEY = "openLyricSlideshow.v1";
	const DEFAULTS = {
		theme: "auto",
		thumbSize: 220,
		loop: false,
		progress: true,
		autoAdvance: 0,
		notesSize: 22,
		/** `auto` (the system's `prefers-reduced-motion`), `full` or `reduced`. */
		motion: "auto"
	};
	const prefs = { ...DEFAULTS };
	try {
		const saved = JSON.parse(globalThis.localStorage?.getItem(PREF_KEY) ?? "null");
		if (saved && typeof saved === "object") {
			for (const key of Object.keys(DEFAULTS)) if (typeof saved[key] === typeof DEFAULTS[key]) prefs[key] = saved[key];
		}
	} catch {}
	function savePrefs() {
		try {
			globalThis.localStorage?.setItem(PREF_KEY, JSON.stringify(prefs));
		} catch {}
	}
	/**
	* Is motion kept down — by the Motion setting, or under `auto` by the
	* system? Then a slide cuts in, a show starts on its slide rather than
	* from black, and only Replay plays a transition.
	*/
	function isMotionReduced() {
		if (prefs.motion === "reduced") return true;
		if (prefs.motion === "full") return false;
		try {
			return Boolean(globalThis.matchMedia?.("(prefers-reduced-motion: reduce)")?.matches);
		} catch {
			return false;
		}
	}
	const slideCount = (count) => t(count === 1 ? "{0} slide" : "{0} slides", count);
	const seconds = (ms) => `${Math.round(ms / 100) / 10}s`;
	const transitionOf = (index) => {
		const transition = slides[index]?.transition;
		return transition && transition.type && transition.type !== "none" ? transition : null;
	};
	/** How the slide comes on, for its labels: its transition, or its lyrics' build. */
	const changeOf = (index) => transitionOf(index) ?? slides[index]?.textTransition ?? null;
	const describeTransition = (index) => {
		const transition = changeOf(index);
		return transition ? `${transition.label || transition.type} ${seconds(transition.durationMs)}` : t("None");
	};
	let toastTimer = 0;
	function toast(message) {
		const element = $("toast");
		element.textContent = message;
		element.hidden = false;
		clearTimeout(toastTimer);
		toastTimer = window.setTimeout(() => {
			element.hidden = true;
		}, 1800);
	}
	function openDialog(id) {
		const dialog = $(id);
		if (typeof dialog.showModal === "function") dialog.showModal();
		else dialog.setAttribute("open", "");
	}
	const THEME_LABELS = {
		auto: t("Theme: match the system"),
		light: t("Theme: light"),
		dark: t("Theme: dark")
	};
	function applyTheme() {
		if (prefs.theme === "light" || prefs.theme === "dark") root.setAttribute("data-theme", prefs.theme);
		else root.removeAttribute("data-theme");
		const button = $("btn-theme");
		button.title = THEME_LABELS[prefs.theme] ?? THEME_LABELS.auto;
		button.setAttribute("aria-label", t("{0} (T to switch)", button.title));
	}
	function cycleTheme() {
		const order = [
			"auto",
			"light",
			"dark"
		];
		prefs.theme = order[(order.indexOf(prefs.theme) + 1) % order.length];
		savePrefs();
		applyTheme();
		toast(THEME_LABELS[prefs.theme]);
	}
	/** The scale each shrinking text box is drawn at, by `slide:element`. */
	const fits = /* @__PURE__ */ new Map();
	const place = (element, box) => {
		element.style.left = `${box.x}px`;
		element.style.top = `${box.y}px`;
		element.style.width = `${box.w}px`;
		element.style.height = `${box.h}px`;
	};
	function drawText(text, scale) {
		const box = h("div", { class: `text-box valign-${text.valign}` });
		place(box, text);
		const [top, right, bottom, left] = text.padding;
		box.style.padding = `${top}px ${right}px ${bottom}px ${left}px`;
		box.style.fontFamily = text.fontFamily;
		box.style.fontSize = `${text.fontSize * scale}px`;
		box.style.fontWeight = text.bold ? "700" : "400";
		box.style.color = text.color;
		box.style.textAlign = text.align;
		if (text.fill) box.style.background = text.fill;
		if (text.border) {
			box.style.outline = `${text.border.width}px solid ${text.border.color}`;
			box.style.outlineOffset = `-${text.border.width}px`;
		}
		const flow = h("div", { class: "text-flow" });
		for (const paragraph of text.paragraphs) flow.append(h("p", null, paragraph || "\xA0"));
		box.append(flow);
		return box;
	}
	/**
	* The words on slide `index`, for screen readers: its pictures' text and
	* its text boxes, line by line. The slides themselves are `aria-hidden`
	* (pictures drawn over and over at every size), so this is what is read.
	*/
	function slideText(index) {
		return (slides[index]?.elements ?? []).flatMap((element) => element.kind === "image" ? [element.alt ?? ""] : element.kind === "text" ? element.paragraphs : []).map((line) => line.trim()).filter(Boolean).join("\n");
	}
	/** Slide `index` at its full size; the stages and thumbnails scale it. */
	function drawSlide(index) {
		const data = slides[index];
		const slide = h("div", {
			class: "slide",
			"aria-hidden": "true"
		});
		slide.style.width = `${W}px`;
		slide.style.height = `${H}px`;
		const background = data?.background ?? {};
		if (typeof background.media === "number" && media[background.media]) slide.style.backgroundImage = `url("${media[background.media]}")`;
		else if (background.color) slide.style.backgroundColor = background.color;
		(data?.elements ?? []).forEach((element, at) => {
			if (element.kind === "image") {
				const src = media[element.media];
				if (src) {
					const image = h("img", {
						alt: element.alt ?? "",
						draggable: "false",
						decoding: "async"
					});
					image.src = src;
					place(image, element);
					const animation = element.animation;
					if (animation) {
						image.dataset.build = animation.type === "out" ? "out" : "in";
						image.dataset.effect = animation.effect;
						image.dataset.direction = animation.direction;
						image.dataset.duration = String(animation.durationMs);
						if (animation.type === "out") {
							image.style.visibility = "hidden";
							image.alt = "";
						}
					}
					slide.append(image);
				}
			} else if (element.kind === "text") slide.append(drawText(element, fits.get(`${index}:${at}`) ?? 1));
		});
		return slide;
	}
	/**
	* Work out the scale each shrinking text box fits its box at, once its
	* fonts have loaded: the largest, to a hundredth, that keeps every line
	* inside.
	*/
	function fitText() {
		const shrinking = [];
		slides.forEach((slide, index) => slide.elements.forEach((element, at) => {
			if (element.kind === "text" && element.isShrinking) shrinking.push({
				key: `${index}:${at}`,
				index,
				text: element
			});
		}));
		if (!shrinking.length) return Promise.resolve();
		const host = h("div", {
			class: "measure",
			"aria-hidden": "true"
		});
		document.body.append(host);
		const boxes = shrinking.map((entry) => {
			const box = drawText(entry.text, 1);
			host.append(box);
			return box;
		});
		const fonts = document.fonts;
		return Promise.race([fonts?.ready ?? Promise.resolve(), new Promise((resolve) => setTimeout(resolve, 2500))]).then(() => {
			shrinking.forEach((entry, at) => {
				const box = boxes[at];
				const flow = box.firstElementChild;
				const [top, , bottom] = entry.text.padding;
				const room = box.clientHeight - top - bottom;
				const fitsAt = (scale) => {
					box.style.fontSize = `${entry.text.fontSize * scale}px`;
					return flow.offsetHeight <= room + .5;
				};
				if (room <= 0 || fitsAt(1)) return;
				let low = .1;
				let high = 1;
				for (let step = 0; step < 8; step++) {
					const middle = (low + high) / 2;
					if (fitsAt(middle)) low = middle;
					else high = middle;
				}
				fits.set(entry.key, Math.floor(low * 100) / 100);
			});
			host.remove();
		});
	}
	const asLayer = (element) => {
		element.classList.add("layer");
		return element;
	};
	const blackLayer = () => asLayer(h("div", { class: "black" }));
	const endLayer = () => asLayer(h("div", { class: "end" }, t("End of slide show. Click or press Esc to exit.")));
	const resolveDirection = (type, direction) => {
		const choices = directions[type];
		if (!Array.isArray(choices) || !choices.length) return "";
		return direction && choices.slice(1).includes(direction) ? direction : choices[0];
	};
	/** A box the slides show in, one at a time, scaled to fit. */
	class Stage {
		host;
		box;
		key = "";
		current = null;
		playback = null;
		constructor(host) {
			this.host = host;
			this.box = h("div", { class: "stage-box" });
			this.box.style.width = `${W}px`;
			this.box.style.height = `${H}px`;
			host.append(this.box);
			if (typeof ResizeObserver === "function") new ResizeObserver(() => this.fit()).observe(host);
			this.fit();
		}
		fit() {
			const width = this.host.clientWidth;
			const height = this.host.clientHeight;
			if (width && height) this.box.style.setProperty("--s", String(Math.max(.01, Math.min(width / W, height / H))));
		}
		/** End a transition under way; whether one was. */
		finishTransition() {
			const playback = this.playback;
			if (!playback) return false;
			this.playback = null;
			playback.finish();
			return true;
		}
		/** Show `layer` as `key`, coming on with `transition` or at once. */
		show(layer, key, transition) {
			this.playback?.finish();
			const from = this.current;
			for (const child of [...this.box.children]) if (child !== from) child.remove();
			this.box.append(layer);
			this.current = layer;
			this.key = key;
			if (!transition || !from) {
				from?.remove();
				this.playback = null;
				return;
			}
			const play = engine.play(this.box, from, layer, {
				type: transition.type,
				direction: transition.direction,
				durationMs: transition.durationMs,
				resolveDirection,
				overlayClassName: "overlay"
			});
			this.playback = play;
			play.finished.then(() => {
				if (this.playback === play) this.playback = null;
			});
		}
		/** Slide `index`, unless it shows already (or `isForced`). */
		showSlide(index, { isAnimated = false, from = null, isForced = false, isRequested = false } = {}) {
			const key = `slide:${index}`;
			if (key === this.key && !isForced) return;
			const plays = isAnimated && (isRequested || !isMotionReduced());
			if (from && plays) this.show(from, "from", null);
			const layer = asLayer(drawSlide(index));
			this.show(layer, key, plays ? transitionOf(index) : null);
			if (plays && !from?.classList.contains("black")) this.build(layer);
		}
		/** Play `layer`'s build, if it has one: what leaves, then what comes on. */
		build(layer) {
			const steps = [...layer.querySelectorAll("[data-build]")].map((element) => ({
				isExit: element.dataset.build === "out",
				element,
				effect: element.dataset.effect ?? "fade",
				direction: element.dataset.direction ?? "",
				durationMs: Number(element.dataset.duration) || 0
			}));
			if (!steps.length) return;
			for (const step of steps) if (step.isExit) step.element.style.removeProperty("visibility");
			const play = engine.playBuild(this.box, {
				exits: steps.filter((step) => step.isExit),
				entrances: steps.filter((step) => !step.isExit)
			});
			this.playback = play;
			play.finished.then(() => {
				if (this.playback === play) this.playback = null;
			});
		}
		clear() {
			this.playback?.finish();
			this.box.replaceChildren();
			this.current = null;
			this.key = "";
		}
	}
	const thumbObserver = typeof ResizeObserver === "function" ? new ResizeObserver((entries) => {
		for (const entry of entries) {
			const slide = entry.target.firstElementChild;
			if (slide && entry.contentRect.width) slide.style.transform = `scale(${entry.contentRect.width / W})`;
		}
	}) : null;
	function makeThumb(index) {
		const box = h("div", { class: "thumb" }, drawSlide(index));
		thumbObserver?.observe(box);
		return box;
	}
	const state = {
		view: "slides",
		slide: 0
	};
	let mode = null;
	const show = {
		isEnded: false,
		cover: null,
		isFullscreen: false,
		isAutoPaused: false
	};
	const hashParams = new URLSearchParams(location.hash.replace(/^#/u, ""));
	const isAudience = hashParams.get("audience") === "1" && !!window.opener;
	let audience = null;
	const clamp = (index) => Math.min(Math.max(0, Math.floor(Number(index)) || 0), Math.max(0, slides.length - 1));
	const mainStage = new Stage($("main-stage"));
	const showStage = new Stage($("show-stage"));
	const presenterStage = new Stage($("p-stage"));
	const nextStage = new Stage($("p-next"));
	function activeStage() {
		if (mode === "show") return showStage;
		if (mode === "presenter") return presenterStage;
		return state.view === "slides" ? mainStage : null;
	}
	function goTo(index, move = {}) {
		if (!slides.length) return;
		state.slide = clamp(index);
		show.isEnded = false;
		render(move);
	}
	function act(action) {
		if (!slides.length) return;
		if (isAudience && mode === "show" && window.opener && !window.opener.closed && [
			"next",
			"prev",
			"first",
			"last",
			"black",
			"white"
		].includes(action)) {
			window.opener.postMessage({
				olSlideshow: 1,
				type: "action",
				action
			}, "*");
			return;
		}
		if (action === "black" || action === "white") {
			show.cover = show.cover === action ? null : action;
			render();
			return;
		}
		if (action === "replay") {
			replay();
			return;
		}
		if (mode && show.cover && (action === "next" || action === "prev")) {
			show.cover = null;
			render();
			return;
		}
		if (action === "next") {
			if (activeStage()?.finishTransition()) return;
			if (mode && show.isEnded) {
				if (mode === "show" && !isAudience) exitMode();
				return;
			}
			if (state.slide + 1 < slides.length) goTo(state.slide + 1, { isAnimated: true });
			else if (mode) if (prefs.loop) goTo(0, { isAnimated: true });
			else {
				show.isEnded = true;
				render();
			}
		} else if (action === "prev") {
			activeStage()?.finishTransition();
			if (mode && show.isEnded) {
				show.isEnded = false;
				render();
			} else if (state.slide > 0) goTo(state.slide - 1);
		} else if (action === "first") goTo(0);
		else if (action === "last") goTo(slides.length - 1);
	}
	/** The slide shown, coming on again from the one before (or black). */
	function replay() {
		const stage = activeStage();
		if (!stage || show.isEnded) return;
		stage.showSlide(state.slide, {
			isAnimated: true,
			isForced: true,
			isRequested: true,
			from: state.slide > 0 ? asLayer(drawSlide(state.slide - 1)) : blackLayer()
		});
		scheduleAuto();
	}
	function setView(view) {
		const next = view === "grid" ? "grid" : "slides";
		state.view = next;
		$("view-slides").hidden = next !== "slides";
		$("view-grid").hidden = next !== "grid";
		for (const tab of document.querySelectorAll(".tabs [data-view]")) tab.setAttribute("aria-selected", String(tab.getAttribute("data-view") === next));
		if (next !== "slides") mainStage.clear();
		else isFilmScrollNeeded = true;
		if (next === "grid") ensureGrid();
		render();
	}
	const wakeLock = {
		isWanted: false,
		sentinel: null,
		isPending: false
	};
	function acquireWakeLock() {
		const api = navigator.wakeLock;
		if (!wakeLock.isWanted || wakeLock.sentinel || wakeLock.isPending || typeof api?.request !== "function" || document.visibilityState === "hidden") return;
		wakeLock.isPending = true;
		Promise.resolve().then(() => api.request("screen")).then((lock) => {
			wakeLock.isPending = false;
			if (!wakeLock.isWanted) {
				lock.release().catch(() => {});
				return;
			}
			wakeLock.sentinel = lock;
			lock.addEventListener?.("release", () => {
				if (wakeLock.sentinel === lock) wakeLock.sentinel = null;
			});
		}, () => {
			wakeLock.isPending = false;
		});
	}
	function holdWakeLock() {
		wakeLock.isWanted = true;
		acquireWakeLock();
	}
	function releaseWakeLock() {
		wakeLock.isWanted = false;
		const lock = wakeLock.sentinel;
		wakeLock.sentinel = null;
		lock?.release().catch(() => {});
	}
	document.addEventListener("visibilitychange", () => {
		if (document.visibilityState === "visible") acquireWakeLock();
	});
	function enterMode(next) {
		if (!slides.length || mode === next) return;
		leaveModeQuietly();
		mode = next;
		holdWakeLock();
		show.isEnded = false;
		show.cover = null;
		show.isAutoPaused = false;
		mainStage.clear();
		$("show").hidden = next !== "show";
		$("presenter").hidden = next !== "presenter";
		if (next === "presenter") startTimer();
		else {
			pokeHud();
			$("show-stage").focus({ preventScroll: true });
		}
	}
	function leaveModeQuietly() {
		if (mode === "show") showStage.clear();
		if (mode === "presenter") {
			presenterStage.clear();
			nextStage.clear();
			stopTimer();
		}
		$("show").hidden = true;
		$("presenter").hidden = true;
		clearTimeout(autoTimer);
		clearJump();
	}
	function exitMode() {
		if (document.fullscreenElement && document.exitFullscreen) document.exitFullscreen().catch(() => {});
		show.isFullscreen = false;
		leaveModeQuietly();
		mode = null;
		releaseWakeLock();
		show.isEnded = false;
		show.cover = null;
		setView(state.view);
	}
	function startShow(from) {
		if (!slides.length) return;
		enterMode("show");
		state.slide = clamp(from ?? 0);
		show.isEnded = false;
		render({
			isAnimated: true,
			isFromBlack: true
		});
		requestFullscreen();
	}
	function startPresenter() {
		enterMode("presenter");
		render({
			isAnimated: true,
			isFromBlack: true
		});
	}
	function requestFullscreen() {
		const element = document.documentElement;
		if (document.fullscreenElement || typeof element.requestFullscreen !== "function") return;
		element.requestFullscreen().then(() => {
			show.isFullscreen = true;
		}).catch(() => {});
	}
	function toggleFullscreen() {
		if (document.fullscreenElement) document.exitFullscreen().catch(() => {});
		else requestFullscreen();
	}
	document.addEventListener("fullscreenchange", () => {
		if (document.fullscreenElement) return;
		if (show.isFullscreen && mode === "show" && !isAudience) {
			show.isFullscreen = false;
			exitMode();
		}
		show.isFullscreen = false;
	});
	function render(move = {}) {
		if (!slides.length) {
			writeHash();
			return;
		}
		if (mode === "show") renderShow(move);
		else if (mode === "presenter") renderPresenter(move);
		else if (state.view === "slides") renderSlidesView(move);
		else renderGridSelection();
		renderFilmstripSelection();
		announceSlide();
		writeHash();
		syncAudience();
		scheduleAuto();
	}
	/**
	* Say the slide now shown, once: its number and its words, in a polite
	* live region, whenever the slide or the view showing it changes.
	*/
	let announced = "";
	function announceSlide() {
		const where = `${mode ?? state.view}:${state.slide}:${show.isEnded}`;
		if (where === announced) return;
		announced = where;
		const live = $("slide-live");
		if (!live) return;
		if (show.isEnded) {
			live.textContent = t("End of slide show. Click or press Esc to exit.");
			return;
		}
		const words = slideText(state.slide);
		live.textContent = [t("Slide {0} of {1}", state.slide + 1, slides.length), words].filter(Boolean).join("\n");
	}
	const fromOf = (move) => move.isFromBlack ? blackLayer() : null;
	function renderSlidesView(move) {
		mainStage.showSlide(state.slide, { isAnimated: move.isAnimated });
		$("main-counter").textContent = t("Slide {0} of {1}", state.slide + 1, slides.length);
		const flags = $("main-flags");
		flags.replaceChildren();
		if (changeOf(state.slide)) flags.append(h("span", {
			class: "chip accent",
			text: t("Transition: {0}", describeTransition(state.slide))
		}));
		renderSide();
	}
	function renderSide() {
		const slide = slides[state.slide];
		$("side").replaceChildren(h("h2", { text: t("Notes") }), slide.notes ? h("div", {
			class: "notes",
			text: slide.notes
		}) : h("p", {
			class: "empty",
			text: t("No speaker notes.")
		}), h("h2", { text: t("Slide") }), h("dl", { class: "kv" }, [
			h("dt", { text: t("Slide") }),
			h("dd", { text: `${state.slide + 1} / ${slides.length}` }),
			h("dt", { text: t("Transition") }),
			h("dd", { text: describeTransition(state.slide) })
		]));
	}
	function renderShow(move) {
		if (show.isEnded) {
			if (showStage.key !== "end") showStage.show(endLayer(), "end", null);
		} else showStage.showSlide(state.slide, {
			isAnimated: move.isAnimated,
			from: fromOf(move),
			isForced: move.isFromBlack
		});
		const cover = $("show-cover");
		cover.hidden = !show.cover;
		cover.classList.toggle("white", show.cover === "white");
		const progress = $("show-progress");
		progress.hidden = !prefs.progress;
		progress.style.width = `${show.isEnded ? 100 : slides.length > 1 ? state.slide / (slides.length - 1) * 100 : 0}%`;
		$("show-counter").textContent = `${state.slide + 1} / ${slides.length}`;
		const auto = $("show-auto");
		auto.hidden = !(prefs.autoAdvance > 0) || isAudience;
		auto.setAttribute("aria-pressed", String(prefs.autoAdvance > 0 && !show.isAutoPaused));
	}
	function renderPresenter(move) {
		presenterStage.showSlide(state.slide, {
			isAnimated: move.isAnimated,
			from: fromOf(move),
			isForced: move.isFromBlack
		});
		$("p-ended").hidden = !show.isEnded;
		$("p-counter").textContent = t("Slide {0} of {1}", state.slide + 1, slides.length);
		let next = show.isEnded ? null : state.slide + 1 < slides.length ? state.slide + 1 : null;
		if (next === null && !show.isEnded && prefs.loop) next = 0;
		if (next === null) {
			nextStage.clear();
			$("p-next-end").hidden = false;
			$("p-next-label").textContent = "";
		} else {
			nextStage.showSlide(next);
			$("p-next-end").hidden = true;
			$("p-next-label").textContent = `${t("Slide {0}", next + 1)}${changeOf(next) ? SEP + describeTransition(next) : ""}`;
		}
		const notes = $("p-notes");
		const slide = slides[state.slide];
		notes.replaceChildren(slide.notes ? slide.notes : h("span", {
			class: "empty",
			text: t("No speaker notes.")
		}));
		root.style.setProperty("--notes-size", `${prefs.notesSize}px`);
		$("p-black").setAttribute("aria-pressed", String(show.cover === "black"));
		$("p-white").setAttribute("aria-pressed", String(show.cover === "white"));
		const cover = $("p-cover");
		cover.hidden = !show.cover;
		cover.classList.toggle("white", show.cover === "white");
	}
	const filmItems = [];
	function buildFilmstrip() {
		const strip = $("filmstrip");
		slides.forEach((slide, index) => {
			const number = h("div", { class: "film-num" }, h("span", { text: String(index + 1) }));
			if (changeOf(index)) number.append(h("span", {
				class: "film-mark",
				text: "T",
				title: t("Transition: {0}", describeTransition(index))
			}));
			if (slide.notes) number.append(h("span", {
				class: "film-mark",
				text: "N",
				title: t("Has speaker notes")
			}));
			const item = h("button", {
				type: "button",
				class: "film-item",
				title: t("Slide {0}. Double-click to present from here", index + 1),
				"aria-label": [t("Slide {0}", index + 1), slideText(index)].filter(Boolean).join("\n"),
				onclick: () => goTo(index, { isAnimated: index > state.slide }),
				ondblclick: () => startShow(index)
			}, [number, makeThumb(index)]);
			filmItems.push(item);
			strip.append(item);
		});
	}
	let lastFilmSlide = -1;
	let isFilmScrollNeeded = true;
	function renderFilmstripSelection() {
		if (lastFilmSlide !== state.slide) {
			filmItems[lastFilmSlide]?.setAttribute("aria-current", "false");
			lastFilmSlide = state.slide;
			filmItems[state.slide]?.setAttribute("aria-current", "true");
			isFilmScrollNeeded = true;
		}
		if (isFilmScrollNeeded && !mode && state.view === "slides" && filmItems[state.slide]) {
			filmItems[state.slide].scrollIntoView?.({
				block: "nearest",
				inline: "nearest"
			});
			isFilmScrollNeeded = false;
		}
	}
	let gridCards = [];
	function ensureGrid() {
		if (gridCards.length || !slides.length) return;
		const grid = $("grid");
		$("grid-size").value = String(prefs.thumbSize);
		root.style.setProperty("--card-w", `${prefs.thumbSize}px`);
		gridCards = slides.map((slide, index) => {
			const foot = h("div", { class: "card-foot" }, h("span", {
				class: "card-num",
				text: String(index + 1)
			}));
			if (changeOf(index)) foot.append(h("span", {
				class: "chip accent",
				text: describeTransition(index),
				title: t("Transition")
			}));
			if (slide.notes) foot.append(h("span", {
				class: "chip",
				text: t("notes"),
				title: slide.notes.slice(0, 300)
			}));
			const open = () => {
				goTo(index);
				setView("slides");
			};
			const card = h("div", {
				class: "card",
				role: "button",
				tabindex: "0",
				"aria-label": t("Slide {0}. Enter opens it.", index + 1),
				title: t("Click to select, double-click to open"),
				"data-slide": String(index),
				onclick: () => goTo(index),
				ondblclick: open,
				onkeydown: (event) => {
					if (event.key === "Enter") {
						event.preventDefault();
						open();
					}
				}
			}, [
				makeThumb(index),
				h("button", {
					type: "button",
					class: "btn small card-play",
					title: t("Present from here"),
					"aria-label": t("Present from slide {0}", index + 1),
					onclick: (event) => {
						event.stopPropagation();
						startShow(index);
					},
					ondblclick: (event) => event.stopPropagation()
				}, [icon("play"), t("Present")]),
				foot
			]);
			grid.append(card);
			return card;
		});
		const noted = slides.filter((slide) => slide.notes).length;
		$("grid-summary").textContent = [slideCount(slides.length), ...noted ? [t("{0} with notes", noted)] : []].join(SEP);
		renderGridSelection();
	}
	function renderGridSelection() {
		for (const card of gridCards) {
			const isCurrent = Number(card.dataset.slide) === state.slide;
			card.setAttribute("aria-current", String(isCurrent));
			if (isCurrent && state.view === "grid" && !mode) card.scrollIntoView?.({ block: "nearest" });
		}
	}
	$("grid-size").addEventListener("input", (event) => {
		prefs.thumbSize = Number(event.target.value) || DEFAULTS.thumbSize;
		root.style.setProperty("--card-w", `${prefs.thumbSize}px`);
		savePrefs();
	});
	function buildTopbar() {
		$("deck-title").textContent = deckName;
		$("deck-title").title = deckName;
		const parts = [slideCount(slides.length)];
		if (deck.exportedAt) parts.push(t("exported {0}", deck.exportedAt));
		if (deck.generator) parts.push(deck.generator);
		$("deck-meta").textContent = parts.join(SEP);
	}
	const timer = {
		startedAt: 0,
		elapsed: 0,
		isRunning: false,
		interval: 0
	};
	const pad2 = (value) => String(value).padStart(2, "0");
	const timerElapsed = () => timer.elapsed + (timer.isRunning ? Date.now() - timer.startedAt : 0);
	function tick() {
		const total = Math.floor(timerElapsed() / 1e3);
		$("p-timer").textContent = `${pad2(Math.floor(total / 3600))}:${pad2(Math.floor(total % 3600 / 60))}:${pad2(total % 60)}`;
		$("p-clock").textContent = (/* @__PURE__ */ new Date()).toLocaleTimeString([], {
			hour: "2-digit",
			minute: "2-digit"
		});
		$("p-pause").setAttribute("aria-pressed", String(!timer.isRunning));
	}
	function startTimer() {
		timer.elapsed = 0;
		timer.startedAt = Date.now();
		timer.isRunning = true;
		clearInterval(timer.interval);
		timer.interval = window.setInterval(tick, 500);
		tick();
	}
	function stopTimer() {
		clearInterval(timer.interval);
	}
	$("p-pause").addEventListener("click", () => {
		if (timer.isRunning) {
			timer.elapsed = timerElapsed();
			timer.isRunning = false;
		} else {
			timer.startedAt = Date.now();
			timer.isRunning = true;
		}
		tick();
	});
	$("p-reset").addEventListener("click", () => {
		timer.elapsed = 0;
		timer.startedAt = Date.now();
		tick();
	});
	const setNotesSize = (size) => {
		prefs.notesSize = Math.min(64, Math.max(10, size));
		savePrefs();
		root.style.setProperty("--notes-size", `${prefs.notesSize}px`);
	};
	$("p-font-down").addEventListener("click", () => setNotesSize(prefs.notesSize - 2));
	$("p-font-up").addEventListener("click", () => setNotesSize(prefs.notesSize + 2));
	$("p-black").addEventListener("click", () => act("black"));
	$("p-white").addEventListener("click", () => act("white"));
	$("p-exit").addEventListener("click", () => exitMode());
	$("p-audience").addEventListener("click", openAudience);
	function openAudience() {
		const url = `${location.href.split("#")[0]}#view=show&audience=1&slide=${state.slide + 1}`;
		audience = window.open(url, "ol-slideshow-audience", `popup,width=${Math.round(W / 2)},height=${Math.round(H / 2)}`);
		if (!audience) toast(t("The browser blocked the audience window. Allow pop-ups for this page."));
	}
	function syncAudience() {
		if (!audience || audience.closed) return;
		audience.postMessage({
			olSlideshow: 1,
			type: "state",
			slide: state.slide,
			isEnded: show.isEnded,
			cover: show.cover
		}, "*");
	}
	window.addEventListener("message", (event) => {
		const data = event.data;
		if (!data || typeof data !== "object" || data.olSlideshow !== 1) return;
		if (data.type === "state" && isAudience && event.source === window.opener) {
			const slide = clamp(data.slide);
			const isAnimated = slide === state.slide + 1 || slide === 0 && state.slide === slides.length - 1;
			state.slide = slide;
			show.isEnded = data.isEnded === true;
			show.cover = data.cover === "black" || data.cover === "white" ? data.cover : null;
			if (mode !== "show") enterMode("show");
			render({ isAnimated });
		} else if (audience && event.source === audience) {
			if (data.type === "hello") syncAudience();
			else if (data.type === "action" && typeof data.action === "string") act(data.action);
		}
	});
	let autoTimer = 0;
	function scheduleAuto() {
		clearTimeout(autoTimer);
		if (!mode || isAudience || show.isAutoPaused || show.isEnded || show.cover || !(prefs.autoAdvance > 0)) return;
		autoTimer = window.setTimeout(() => act("next"), prefs.autoAdvance * 1e3);
	}
	let hudTimer = 0;
	function pokeHud() {
		const element = $("show");
		element.classList.add("hud-visible");
		element.classList.remove("hide-cursor");
		clearTimeout(hudTimer);
		hudTimer = window.setTimeout(() => {
			if (document.activeElement?.closest(".hud")) $("show-stage").focus({ preventScroll: true });
			element.classList.remove("hud-visible");
			element.classList.add("hide-cursor");
		}, 2500);
	}
	let jumpBuffer = "";
	let jumpTimer = 0;
	function pushJump(digit) {
		jumpBuffer = (jumpBuffer + digit).slice(-4);
		const element = $("show-jump");
		element.textContent = t("Go to slide {0}", jumpBuffer);
		element.hidden = mode !== "show";
		if (mode !== "show") toast(t("Go to slide {0}", jumpBuffer));
		clearTimeout(jumpTimer);
		jumpTimer = window.setTimeout(clearJump, 3e3);
	}
	function clearJump() {
		jumpBuffer = "";
		clearTimeout(jumpTimer);
		$("show-jump").hidden = true;
	}
	const showElement = $("show");
	showElement.addEventListener("mousemove", pokeHud);
	let swipe = null;
	let isClickSuppressed = false;
	showElement.addEventListener("pointerdown", (event) => {
		swipe = event.pointerType === "mouse" ? null : {
			x: event.clientX,
			y: event.clientY
		};
	});
	showElement.addEventListener("pointerup", (event) => {
		if (!swipe) return;
		const dx = event.clientX - swipe.x;
		const dy = event.clientY - swipe.y;
		swipe = null;
		if (Math.abs(dx) > 50 && Math.abs(dx) > Math.abs(dy)) {
			isClickSuppressed = true;
			act(dx < 0 ? "next" : "prev");
		}
	});
	showElement.addEventListener("click", (event) => {
		if (isClickSuppressed) {
			isClickSuppressed = false;
			return;
		}
		if (event.target.closest(".hud")) return;
		if (show.isEnded && !isAudience) {
			exitMode();
			return;
		}
		act("next");
	});
	let wheelAt = 0;
	showElement.addEventListener("wheel", (event) => {
		if (Math.abs(event.deltaY) < 4 || Date.now() - wheelAt < 350) return;
		wheelAt = Date.now();
		act(event.deltaY > 0 ? "next" : "prev");
	}, { passive: true });
	$("show-auto").addEventListener("click", () => {
		show.isAutoPaused = !show.isAutoPaused;
		render();
	});
	$("show-fullscreen").addEventListener("click", toggleFullscreen);
	$("show-help").addEventListener("click", () => openDialog("dlg-help"));
	$("show-exit").addEventListener("click", () => exitMode());
	$("main-stage").addEventListener("click", () => act("next"));
	const NEXT_KEYS = [
		"ArrowRight",
		"ArrowDown",
		"PageDown",
		" ",
		"Enter",
		"n",
		"N"
	];
	const PREVIOUS_KEYS = [
		"ArrowLeft",
		"ArrowUp",
		"PageUp",
		"Backspace",
		"p",
		"P"
	];
	function handleModeKey(event) {
		const key = event.key;
		if (/^[0-9]$/u.test(key)) {
			pushJump(key);
			return true;
		}
		if (key === "Enter" && jumpBuffer) {
			const number = Number.parseInt(jumpBuffer, 10);
			clearJump();
			if (number >= 1 && number <= slides.length && !isAudience) goTo(number - 1, { isAnimated: true });
			return true;
		}
		if (NEXT_KEYS.includes(key)) act("next");
		else if (PREVIOUS_KEYS.includes(key)) act("prev");
		else if (key === "Home") act("first");
		else if (key === "End") act("last");
		else if (key === "b" || key === "B" || key === ".") act("black");
		else if (key === "w" || key === "W" || key === ",") act("white");
		else if (key === "r" || key === "R") act("replay");
		else if (key === "a" || key === "A") {
			if (prefs.autoAdvance > 0) {
				show.isAutoPaused = !show.isAutoPaused;
				toast(show.isAutoPaused ? t("Auto-advance paused") : t("Auto-advance on"));
				render();
			}
		} else if (key === "f" || key === "F") toggleFullscreen();
		else if (key === "h" || key === "H" || key === "?") openDialog("dlg-help");
		else if (key === "Escape") {
			if (jumpBuffer) clearJump();
			else if (show.cover) {
				show.cover = null;
				render();
			} else if (!isAudience) exitMode();
		} else return false;
		return true;
	}
	function handleViewKey(event) {
		const key = event.key;
		if (key === "F5") {
			startShow(event.shiftKey ? state.slide : 0);
			return true;
		}
		if (event.shiftKey && key !== "?") return false;
		if (key === "ArrowRight" || key === " " || key === "ArrowDown" || key === "PageDown") act("next");
		else if (key === "ArrowLeft" || key === "ArrowUp" || key === "PageUp") act("prev");
		else if (key === "Home") act("first");
		else if (key === "End") act("last");
		else if (key === "r" || key === "R") act("replay");
		else if (key === "s" || key === "S") setView("slides");
		else if (key === "g" || key === "G") setView("grid");
		else if (key === "p" || key === "P") startPresenter();
		else if (key === "t" || key === "T") cycleTheme();
		else if (key === "?" || key === "h" || key === "H") openDialog("dlg-help");
		else return false;
		return true;
	}
	document.addEventListener("keydown", (event) => {
		if (event.defaultPrevented || event.isComposing || event.metaKey || event.ctrlKey || event.altKey) return;
		if (document.querySelector("dialog[open]")) return;
		const target = event.target;
		if (target?.closest?.("input, textarea, select, [contenteditable=\"true\"]")) return;
		if (!mode && target?.closest?.(".card, button, a") && (event.key === "Enter" || event.key === " ")) return;
		if (mode ? handleModeKey(event) : handleViewKey(event)) event.preventDefault();
	});
	for (const tab of document.querySelectorAll(".tabs [data-view]")) tab.addEventListener("click", () => setView(tab.getAttribute("data-view") ?? "slides"));
	for (const button of document.querySelectorAll("[data-act]")) button.addEventListener("click", (event) => {
		event.stopPropagation();
		act(button.getAttribute("data-act") ?? "");
	});
	$("btn-present").addEventListener("click", () => startShow(0));
	$("btn-present-here").addEventListener("click", () => startShow(state.slide));
	$("btn-presenter").addEventListener("click", startPresenter);
	$("btn-theme").addEventListener("click", cycleTheme);
	$("btn-help").addEventListener("click", () => openDialog("dlg-help"));
	$("btn-replay").addEventListener("click", () => act("replay"));
	function syncSettingsForm() {
		$("set-theme").value = prefs.theme;
		$("set-motion").value = prefs.motion;
		$("set-loop").checked = prefs.loop;
		$("set-progress").checked = prefs.progress;
		$("set-auto").value = String(prefs.autoAdvance);
	}
	$("btn-settings").addEventListener("click", () => {
		syncSettingsForm();
		openDialog("dlg-settings");
	});
	$("dlg-settings").addEventListener("change", () => {
		prefs.theme = $("set-theme").value;
		prefs.motion = ["full", "reduced"].includes($("set-motion").value) ? $("set-motion").value : "auto";
		prefs.loop = $("set-loop").checked;
		prefs.progress = $("set-progress").checked;
		prefs.autoAdvance = Math.min(3600, Math.max(0, Math.round(Number($("set-auto").value) || 0)));
		savePrefs();
		applyTheme();
		render();
	});
	for (const dialog of document.querySelectorAll("dialog")) {
		dialog.addEventListener("close", () => {
			if (mode === "show") $("show-stage").focus({ preventScroll: true });
		});
		dialog.addEventListener("keydown", (event) => event.stopPropagation());
	}
	document.addEventListener("click", (event) => {
		const control = event.target.closest?.("button, .card");
		if (control && event.detail > 0 && !control.closest("dialog")) control.blur();
	});
	let writtenHash = "";
	function writeHash() {
		if (isAudience || !slides.length) return;
		const params = new URLSearchParams();
		params.set("view", mode ?? state.view);
		params.set("slide", String(state.slide + 1));
		const hash = `#${params}`;
		if (hash === location.hash) return;
		writtenHash = hash;
		try {
			history.replaceState(null, "", hash);
		} catch {
			try {
				location.hash = hash;
			} catch {}
		}
	}
	function applyHash(params) {
		const view = params.get("view") ?? "slides";
		if (!slides.length) {
			setView(view);
			return;
		}
		state.slide = clamp((Number(params.get("slide")) || 1) - 1);
		if (view === "show" || view === "presenter") {
			if (mode !== view) enterMode(view);
			render();
		} else {
			if (mode) {
				leaveModeQuietly();
				mode = null;
				releaseWakeLock();
			}
			setView(view);
		}
	}
	window.addEventListener("hashchange", () => {
		if (location.hash === writtenHash || isAudience) return;
		applyHash(new URLSearchParams(location.hash.replace(/^#/u, "")));
	});
	applyTheme();
	buildTopbar();
	if (!slides.length) {
		$("view-slides").replaceChildren(h("p", {
			class: "empty-deck",
			text: t("This slide show has no slides.")
		}));
		for (const id of [
			"btn-present",
			"btn-present-here",
			"btn-presenter"
		]) $(id).disabled = true;
		applyHash(hashParams);
		return;
	}
	fitText().then(() => {
		buildFilmstrip();
		applyHash(hashParams);
		root.setAttribute("data-ready", "");
		if (isAudience) window.opener.postMessage({
			olSlideshow: 1,
			type: "hello"
		}, "*");
	});
}
//#endregion
//#region src/plugins/OpenLyric/preview/controller/pptx/html-presentation.ts
/**
* **Download as HTML**: the deck as one self-contained web page — a slide
* show that runs in any browser, offline, with nothing beside it.
*
* It is the very deck the `.pptx` gets (`PptxPresentation.toData()`): the
* same backgrounds, pictures, text boxes, notes and transitions, laid out in
* pixels of a 1920×1080 slide. Every picture is in the page as a `data:` URI,
* once however many slides show it. The page's script is two functions'
* own source: the slideshow viewer (`./html-slideshow-runtime.ts`) and the
* transition engine the PowerPoint dialog's stage plays
* (`./transition-preview.ts`) — so a transition looks there as it did on the
* stage.
*
* Building the page needs no DOM; only the page itself does, when opened.
*/
var HTML_MIME_TYPE = "text/html;charset=utf-8";
/** The slide the page draws on, in pixels: the deck's 13.333 × 7.5 in at 144 px/in. */
var SLIDE_WIDTH_PX = 1920;
var POINTS_PER_INCH = 72;
/** PowerPoint's theme font, for text that names none. */
var THEME_FONT = "Calibri, Carlito, Arial, sans-serif";
/**
* The viewer's words its script writes, keyed as the page carries their
* translations (`OpenLyricHtmlDeck.strings`). `{0}` takes a number or a name.
* The page's markup (buttons, help, settings) is translated as it is written,
* so it is listed from {@link BODY} instead.
*/
var OPEN_LYRIC_HTML_SCRIPT_STRINGS = Object.freeze([
	"Slide show",
	"{0} slide",
	"{0} slides",
	"None",
	"Theme: match the system",
	"Theme: light",
	"Theme: dark",
	"{0} (T to switch)",
	"End of slide show. Click or press Esc to exit.",
	"Slide {0} of {1}",
	"Transition: {0}",
	"Notes",
	"No speaker notes.",
	"Slide",
	"Transition",
	"Slide {0}",
	"Has speaker notes",
	"Slide {0}. Double-click to present from here",
	"notes",
	"Slide {0}. Enter opens it.",
	"Click to select, double-click to open",
	"Present from here",
	"Present from slide {0}",
	"Present",
	"{0} with notes",
	"exported {0}",
	"The browser blocked the audience window. Allow pop-ups for this page.",
	"Go to slide {0}",
	"Auto-advance paused",
	"Auto-advance on",
	"This slide show has no slides."
]);
var round = (value) => Math.round(value * 100) / 100;
function escapeHtml(value) {
	return String(value ?? "").replaceAll("&", "&amp;").replaceAll("<", "&lt;").replaceAll(">", "&gt;").replaceAll("\"", "&quot;");
}
/** `RRGGBB` (or `#RRGGBB`) as a CSS colour; `fallback` for anything else. */
function toCssColor(color, fallback) {
	const hex = String(color ?? "").trim().replace(/^#/u, "").toUpperCase();
	return /^[0-9A-F]{6}$/u.test(hex) ? `#${hex}` : fallback;
}
/** A face the deck names, as a CSS font-family list ending on the theme font. */
function toFontFamily(fontFace) {
	const face = String(fontFace ?? "").replace(/[;{}<>\\]/gu, "").trim();
	if (!face) return THEME_FONT;
	return `${/[,"']/u.test(face) ? face : `"${face}"`}, ${THEME_FONT}`;
}
/** The date `value` as `YYYY-MM-DD HH:MM`, local time. */
function formatExportedAt(value) {
	if (typeof value === "string") return value;
	const date = value ?? /* @__PURE__ */ new Date();
	const pad = (number) => String(number).padStart(2, "0");
	return `${date.getFullYear()}-${pad(date.getMonth() + 1)}-${pad(date.getDate())} ${pad(date.getHours())}:${pad(date.getMinutes())}`;
}
/** `translate(text)`, or `text` when there is no translator or it fails. */
function translateWith(translate, text) {
	if (typeof translate !== "function") return text;
	try {
		const translated = translate(text);
		return typeof translated === "string" && translated.trim() ? translated : text;
	} catch {
		return text;
	}
}
var unescapeHtml = (value) => value.replaceAll("&quot;", "\"").replaceAll("&lt;", "<").replaceAll("&gt;", ">").replaceAll("&amp;", "&");
/** The attributes of the page's markup that hold words. */
var MARKUP_ATTRIBUTE = /\b(title|aria-label|placeholder)="([^"]*)"/gu;
/** Elements whose text is a key's or the address's own: never translated. */
var VERBATIM_TAG = /^<(\/?)(kbd|code)\b/iu;
var hasWords = (text) => /\p{L}{2,}/u.test(text);
/**
* Every run of words in `markup` — text and the attributes that hold words —
* through `visit`, which returns what to write in its place. Text in `<kbd>`
* and `<code>` is a key or an address, and is left as it is.
*/
function mapMarkupWords(markup, visit) {
	let verbatim = 0;
	return markup.replace(/(<[^>]*>)|([^<]+)/gu, (token, tag, text) => {
		if (tag) {
			const verbatimTag = VERBATIM_TAG.exec(tag);
			if (verbatimTag) verbatim = Math.max(0, verbatim + (verbatimTag[1] ? -1 : 1));
			return tag.replace(MARKUP_ATTRIBUTE, (attribute, name, value) => {
				const english = unescapeHtml(value);
				return hasWords(english) ? `${name}="${escapeHtml(visit(english))}"` : attribute;
			});
		}
		const match = /^(\s*)([\s\S]*?)(\s*)$/u.exec(text);
		const core = unescapeHtml(match?.[2] ?? "");
		if (verbatim || !hasWords(core)) return token;
		return `${match?.[1] ?? ""}${escapeHtml(visit(core)).replaceAll("&quot;", "\"")}${match?.[3] ?? ""}`;
	});
}
/**
* The deck `data` as the page carries it: geometry in pixels, colours and
* fonts as CSS, pictures once each in `media`, each transition resolved.
*/
function buildOpenLyricHtmlDeck(data, { title = "", exportedAt, translate } = {}) {
	const pxPerInch = SLIDE_WIDTH_PX / data.width;
	const width = SLIDE_WIDTH_PX;
	const height = Math.round(data.height * pxPerInch);
	const pxPerPoint = pxPerInch / POINTS_PER_INCH;
	const media = [];
	const mediaIndex = /* @__PURE__ */ new Map();
	const mediaOf = (dataUri) => {
		let index = mediaIndex.get(dataUri);
		if (index === void 0) {
			index = media.length;
			media.push(dataUri);
			mediaIndex.set(dataUri, index);
		}
		return index;
	};
	/** Inches (or a `'50%'` share of `totalPx`) as pixels. */
	const toPx = (value, totalPx, fallbackPx) => {
		if (typeof value === "string" && value.trim().endsWith("%")) {
			const percent = Number.parseFloat(value);
			return Number.isFinite(percent) ? round(percent / 100 * totalPx) : fallbackPx;
		}
		const inches = Number(value);
		return value === void 0 || value === null || !Number.isFinite(inches) ? fallbackPx : round(inches * pxPerInch);
	};
	const boxOf = (options) => ({
		x: toPx(options.x, width, 0),
		y: toPx(options.y, height, 0),
		w: toPx(options.w, width, width),
		h: toPx(options.h, height, height)
	});
	/** `[left, right, bottom, top]` points, or one for all, as top/right/bottom/left px. */
	const paddingOf = (margin) => {
		const px = (value) => {
			const points = Number(value);
			return Number.isFinite(points) && points > 0 ? round(points * pxPerPoint) : 0;
		};
		if (Array.isArray(margin)) {
			const [left = 0, right = 0, bottom = 0, top = 0] = margin;
			return [
				px(top),
				px(right),
				px(bottom),
				px(left)
			];
		}
		const all = px(margin);
		return [
			all,
			all,
			all,
			all
		];
	};
	const transitionOf = (transition) => {
		const spec = transition ? getOpenLyricPowerPointTransitionSpec(transition.type) : null;
		if (!transition || !spec) return null;
		return {
			type: spec.id,
			label: translateWith(translate, spec.label),
			direction: resolveOpenLyricPowerPointTransitionDirection(spec.id, transition.direction),
			durationMs: getOpenLyricPowerPointTransitionDurationMs(spec.id, transition.speed)
		};
	};
	/**
	* A slide whose lyrics come on by themselves, for its labels: the effect
	* its pictures play (the one coming on) — "Wipe (Text only)" — and how
	* long the whole build takes, what leaves and then what comes on.
	*/
	const textTransitionOf = (slide) => {
		const animations = slide.elements.flatMap((element) => element.kind === "image" && element.options.animation ? [element.options.animation] : []);
		if (!animations.length) return null;
		const lengthOf = (type) => Math.max(0, ...animations.filter((animation) => animation.type === "out" === (type === "out")).map((animation) => Math.max(0, Number(animation.durationMs) || 0)));
		const shown = animations.find((animation) => animation.type !== "out") ?? animations[0];
		const label = OPEN_LYRIC_POWERPOINT_TEXT_EFFECT_LABELS[shown.effect] ?? shown.effect;
		return {
			type: shown.effect,
			label: `${translateWith(translate, label)} (${translateWith(translate, "Text only")})`,
			direction: resolveOpenLyricPowerPointTextDirection(shown.effect, shown.direction),
			durationMs: lengthOf("out") + lengthOf("in")
		};
	};
	const slides = data.slides.map((slide) => {
		const textColor = toCssColor(slide.color, "#000000");
		return {
			background: slide.background?.data ? { media: mediaOf(slide.background.data) } : slide.background?.color ? { color: toCssColor(slide.background.color, "#FFFFFF") } : {},
			elements: slide.elements.map((element) => {
				if (element.kind === "image") {
					const { animation } = element.options;
					return {
						kind: "image",
						...boxOf(element.options),
						media: mediaOf(element.options.data),
						alt: String(element.options.description ?? "").trim(),
						...animation ? { animation: {
							type: animation.type === "out" ? "out" : "in",
							effect: animation.effect,
							direction: resolveOpenLyricPowerPointTextDirection(animation.effect, animation.direction),
							durationMs: Math.max(0, Number(animation.durationMs) || 0)
						} } : {}
					};
				}
				const { options } = element;
				return {
					kind: "text",
					...boxOf(options),
					paragraphs: element.text.split("\n"),
					fontFamily: toFontFamily(options.fontFace),
					fontSize: round((Number(options.fontSize) || 18) * pxPerPoint),
					bold: options.bold === true,
					color: toCssColor(options.color, textColor),
					align: options.align ?? "left",
					valign: options.valign ?? "top",
					padding: paddingOf(options.margin),
					fill: options.fill?.color ? toCssColor(options.fill.color, "") : "",
					border: options.line?.color ? {
						color: toCssColor(options.line.color, "#000000"),
						width: round((Number(options.line.width) || 1) * pxPerPoint)
					} : null,
					isShrinking: options.fit === "shrink"
				};
			}),
			notes: slide.notes.trim(),
			transition: transitionOf(slide.transition),
			textTransition: textTransitionOf(slide)
		};
	});
	const directions = {};
	for (const spec of OPEN_LYRIC_POWERPOINT_TRANSITION_SPECS) {
		const choices = listOpenLyricPowerPointTransitionDirections(spec.id).map(([value]) => value);
		if (choices.length) directions[spec.id] = [resolveOpenLyricPowerPointTransitionDirection(spec.id, void 0), ...choices];
	}
	const strings = {};
	for (const text of OPEN_LYRIC_HTML_SCRIPT_STRINGS) {
		const translated = translateWith(translate, text);
		if (translated !== text) strings[text] = translated;
	}
	return {
		title: String(title ?? "").trim(),
		generator: "Open Lyric",
		exportedAt: formatExportedAt(exportedAt),
		width,
		height,
		media,
		directions,
		slides,
		...Object.keys(strings).length ? { strings } : {}
	};
}
var STYLE = `
:root {
  color-scheme: light;
  --bg: #eef0f3;
  --panel: #ffffff;
  --panel-2: #f4f5f7;
  --text: #1c2026;
  --muted: #5b6370;
  --border: #d7dbe2;
  --accent: #2b65d9;
  --accent-soft: rgba(43, 101, 217, 0.12);
  --on-accent: #ffffff;
  --surround: #d5d9e0;
  --shadow: 0 1px 2px rgba(0, 0, 0, 0.08), 0 2px 8px rgba(0, 0, 0, 0.06);
  --radius: 8px;
  --aspect: 16 / 9;
  --card-w: 220px;
  --notes-size: 22px;
}
@media (prefers-color-scheme: dark) {
  :root:not([data-theme="light"]) {
    color-scheme: dark;
    --bg: #15171b; --panel: #1e2126; --panel-2: #272b31; --text: #e6e8eb; --muted: #9ca3ae;
    --border: #353a42; --accent: #6b9bf2; --accent-soft: rgba(107, 155, 242, 0.18); --on-accent: #0b1222;
    --surround: #0e1013; --shadow: 0 1px 2px rgba(0, 0, 0, 0.4), 0 2px 8px rgba(0, 0, 0, 0.3);
  }
}
:root[data-theme="dark"] {
  color-scheme: dark;
  --bg: #15171b; --panel: #1e2126; --panel-2: #272b31; --text: #e6e8eb; --muted: #9ca3ae;
  --border: #353a42; --accent: #6b9bf2; --accent-soft: rgba(107, 155, 242, 0.18); --on-accent: #0b1222;
  --surround: #0e1013; --shadow: 0 1px 2px rgba(0, 0, 0, 0.4), 0 2px 8px rgba(0, 0, 0, 0.3);
}
* { box-sizing: border-box; }
html, body { height: 100%; }
body {
  margin: 0; display: flex; flex-direction: column; overflow: hidden;
  background: var(--bg); color: var(--text);
  font: 14px/1.45 system-ui, -apple-system, "Segoe UI", Roboto, sans-serif;
}
button, select, input { font: inherit; color: inherit; }
[hidden] { display: none !important; }
h1, h2, h3 { line-height: 1.25; }
svg { width: 16px; height: 16px; flex: none; fill: none; stroke: currentColor; stroke-width: 2; stroke-linecap: round; stroke-linejoin: round; }
.btn {
  display: inline-flex; align-items: center; justify-content: center; gap: 6px;
  height: 32px; padding: 0 10px; border: 1px solid var(--border); border-radius: 6px;
  background: var(--panel); cursor: pointer; white-space: nowrap; color: var(--text);
}
.btn:hover { background: var(--panel-2); }
.btn:disabled { opacity: 0.45; cursor: default; }
.btn:focus-visible, .film-item:focus-visible, .card:focus-visible, .tabs button:focus-visible { outline: 2px solid var(--accent); outline-offset: 2px; }
.btn.primary { background: var(--accent); border-color: var(--accent); color: var(--on-accent); }
.btn.icon { width: 32px; padding: 0; }
.btn.small { height: 26px; padding: 0 8px; font-size: 12px; }
.btn[aria-pressed="true"] { background: var(--accent-soft); border-color: var(--accent); color: var(--accent); }
.chip { display: inline-flex; align-items: center; height: 22px; padding: 0 8px; border-radius: 11px; background: var(--panel-2); color: var(--muted); font-size: 12px; white-space: nowrap; }
.chip.accent { background: var(--accent-soft); color: var(--accent); }
.spacer { flex: 1; }
.muted, .empty { color: var(--muted); }
.topbar { display: flex; align-items: center; gap: 16px; padding: 8px 14px; background: var(--panel); border-bottom: 1px solid var(--border); }
.deck { min-width: 0; flex: 1; }
.deck-title { font-weight: 650; font-size: 15px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
.deck-meta { color: var(--muted); font-size: 12px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
.tabs { display: flex; gap: 2px; padding: 2px; border-radius: 8px; background: var(--panel-2); }
.tabs button { border: 0; background: none; padding: 5px 12px; border-radius: 6px; cursor: pointer; color: var(--muted); }
.tabs button[aria-selected="true"] { background: var(--panel); color: var(--text); box-shadow: var(--shadow); }
.actions { display: flex; gap: 6px; }
.view { flex: 1; min-height: 0; }
#view-slides { display: grid; grid-template-columns: 200px minmax(0, 1fr) 300px; }
.filmstrip { overflow-y: auto; padding: 10px; display: flex; flex-direction: column; gap: 8px; border-right: 1px solid var(--border); background: var(--panel); }
.film-item { display: grid; grid-template-columns: 26px 1fr; gap: 6px; align-items: start; padding: 4px; border: 2px solid transparent; border-radius: var(--radius); background: none; cursor: pointer; text-align: left; }
.film-item[aria-current="true"] { border-color: var(--accent); background: var(--accent-soft); }
.film-num { display: flex; flex-direction: column; align-items: center; gap: 3px; font-size: 12px; color: var(--muted); }
.film-mark { font-size: 10px; line-height: 14px; padding: 0 3px; border-radius: 3px; background: var(--panel-2); }
.thumb { position: relative; aspect-ratio: var(--aspect); overflow: hidden; border-radius: 4px; background: #000; box-shadow: var(--shadow); }
.thumb > .slide { position: absolute; left: 0; top: 0; transform-origin: 0 0; transform: scale(0.1); }
.stage-col { display: flex; flex-direction: column; min-width: 0; min-height: 0; background: var(--surround); }
.stage { position: relative; overflow: hidden; flex: 1; min-height: 0; cursor: pointer; }
.stage:focus { outline: none; }
.stage-box { position: absolute; left: 50%; top: 50%; overflow: hidden; background: #000; transform: translate(-50%, -50%) scale(var(--s, 0.3)); box-shadow: 0 0 0 1px rgba(0, 0, 0, 0.2); isolation: isolate; }
.stage-bar { display: flex; align-items: center; gap: 6px; padding: 8px 12px; background: var(--panel); border-top: 1px solid var(--border); }
.counter { min-width: 110px; text-align: center; font-variant-numeric: tabular-nums; color: var(--muted); }
.flags { display: flex; gap: 6px; flex-wrap: wrap; }
.side { overflow-y: auto; padding: 14px 16px; border-left: 1px solid var(--border); background: var(--panel); }
.side h2 { margin: 14px 0 6px; font-size: 12px; text-transform: uppercase; letter-spacing: 0.06em; color: var(--muted); }
.side h2:first-child { margin-top: 0; }
.notes { white-space: pre-wrap; font-size: 15px; }
.kv { display: grid; grid-template-columns: auto 1fr; gap: 4px 12px; margin: 0; }
.kv dt { color: var(--muted); }
.kv dd { margin: 0; }
#view-grid { display: flex; flex-direction: column; }
.toolbar { display: flex; align-items: center; gap: 14px; padding: 8px 14px; background: var(--panel); border-bottom: 1px solid var(--border); }
.toolbar label { display: flex; align-items: center; gap: 8px; }
.grid-scroll { flex: 1; overflow-y: auto; padding: 16px; }
.grid { display: grid; gap: 16px; grid-template-columns: repeat(auto-fill, minmax(var(--card-w), 1fr)); }
.card { position: relative; padding: 6px; border: 2px solid transparent; border-radius: var(--radius); background: var(--panel); box-shadow: var(--shadow); cursor: pointer; }
.card[aria-current="true"] { border-color: var(--accent); }
.card-play { position: absolute; top: 12px; right: 12px; opacity: 0; transition: opacity 120ms; }
.card:hover .card-play, .card:focus-within .card-play { opacity: 1; }
.card-foot { display: flex; align-items: center; gap: 6px; padding-top: 6px; flex-wrap: wrap; }
.card-num { font-weight: 600; min-width: 18px; }
.empty-deck { margin: auto; padding: 40px; text-align: center; color: var(--muted); }
.slide { overflow: hidden; background-size: 100% 100%; background-repeat: no-repeat; }
/* Every layer of a stage — and a transition's pieces — lies over the whole box. */
.stage-box > .layer { position: absolute; left: 0; top: 0; width: 100%; height: 100%; backface-visibility: hidden; }
.slide img { position: absolute; display: block; object-fit: fill; user-select: none; pointer-events: none; }
.black { background: #000; }
.end { background: #000; color: #d8d8d8; display: flex; justify-content: center; padding-top: 48px; font: 36px/1.3 system-ui, sans-serif; }
.overlay { position: absolute; inset: 0; z-index: 4; pointer-events: none; }
.text-box { position: absolute; display: flex; flex-direction: column; line-height: 1.2; white-space: pre-wrap; overflow-wrap: break-word; }
.text-box.valign-middle { justify-content: center; }
.text-box.valign-bottom { justify-content: flex-end; }
.text-box p { margin: 0; }
.measure { position: fixed; left: -100000px; top: 0; width: 1920px; height: 1080px; visibility: hidden; pointer-events: none; }
.presenter { position: fixed; inset: 0; z-index: 50; display: grid; grid-template-columns: minmax(0, 1.6fr) minmax(280px, 1fr); grid-template-rows: minmax(0, 1fr) auto; gap: 12px; padding: 12px; background: var(--bg); }
.p-main, .p-side { display: flex; flex-direction: column; gap: 8px; min-height: 0; }
.p-head { display: flex; align-items: center; gap: 8px; color: var(--muted); font-size: 12px; text-transform: uppercase; letter-spacing: 0.06em; }
.p-stage-wrap, .p-next-wrap { position: relative; flex: 1; min-height: 0; background: var(--surround); border-radius: var(--radius); overflow: hidden; }
.p-next-wrap { flex: 0 0 auto; aspect-ratio: var(--aspect); }
.p-stage-wrap .stage, .p-next-wrap .stage { position: absolute; inset: 0; }
.p-overlay { position: absolute; inset: 0; display: grid; place-items: center; background: rgba(0, 0, 0, 0.75); color: #fff; font-size: 18px; }
.p-cover { position: absolute; inset: 0; background: #000; opacity: 0.85; }
.p-cover.white { background: #fff; }
.p-notes { flex: 1; overflow-y: auto; padding: 12px 14px; border-radius: var(--radius); background: var(--panel); white-space: pre-wrap; font-size: var(--notes-size); line-height: 1.4; }
.p-bar { grid-column: 1 / -1; display: flex; align-items: center; gap: 8px; padding: 8px 10px; border-radius: var(--radius); background: var(--panel); }
.timer { font: 600 20px/1 ui-monospace, SFMono-Regular, Menlo, monospace; min-width: 110px; text-align: center; }
.clock { color: var(--muted); font-variant-numeric: tabular-nums; }
.show { position: fixed; inset: 0; z-index: 100; background: #000; }
.show .stage { position: absolute; inset: 0; }
.show .stage-box { box-shadow: none; }
.show.hide-cursor, .show.hide-cursor .stage { cursor: none; }
.progress { position: absolute; left: 0; bottom: 0; height: 3px; background: var(--accent); transition: width 200ms; z-index: 3; }
.cover { position: absolute; inset: 0; background: #000; z-index: 5; }
.cover.white { background: #fff; }
.jump { position: absolute; top: 20px; left: 50%; transform: translateX(-50%); padding: 8px 16px; border-radius: 8px; background: rgba(0, 0, 0, 0.7); color: #fff; font-size: 18px; z-index: 6; }
.hud { position: absolute; left: 50%; bottom: 18px; transform: translateX(-50%); display: flex; align-items: center; gap: 6px; padding: 6px 8px; border-radius: 10px; background: rgba(20, 20, 20, 0.8); color: #fff; opacity: 0; transition: opacity 200ms; z-index: 7; }
.hud .btn { background: transparent; border-color: transparent; color: #fff; }
.hud .btn:hover { background: rgba(255, 255, 255, 0.12); }
.hud .counter { color: #ddd; min-width: 70px; }
.show.hud-visible .hud, .hud:focus-within { opacity: 1; }
dialog { border: 1px solid var(--border); border-radius: 12px; padding: 0; background: var(--panel); color: var(--text); box-shadow: var(--shadow); width: min(520px, 92vw); }
dialog::backdrop { background: rgba(0, 0, 0, 0.45); }
.dlg-head { display: flex; align-items: center; justify-content: space-between; padding: 12px 16px; border-bottom: 1px solid var(--border); }
.dlg-head h2 { margin: 0; font-size: 16px; }
.dlg-body { padding: 14px 16px 18px; display: grid; gap: 12px; }
.dlg-body h3 { margin: 6px 0 0; font-size: 13px; color: var(--muted); }
.field { display: grid; gap: 4px; }
.field select, .field input { height: 32px; padding: 0 8px; border: 1px solid var(--border); border-radius: 6px; background: var(--panel-2); }
.check { display: flex; align-items: center; gap: 8px; }
.keys { width: 100%; border-collapse: collapse; }
.keys td { padding: 4px 0; vertical-align: top; }
.keys td:first-child { padding-right: 12px; white-space: nowrap; }
kbd { display: inline-block; min-width: 22px; padding: 1px 6px; margin: 0 2px 2px 0; border: 1px solid var(--border); border-bottom-width: 2px; border-radius: 4px; background: var(--panel-2); font: 12px/1.4 ui-monospace, Menlo, monospace; text-align: center; }
.toast { position: fixed; left: 50%; bottom: 28px; transform: translateX(-50%); padding: 8px 14px; border-radius: 8px; background: rgba(20, 20, 20, 0.9); color: #fff; z-index: 200; }
.fatal { margin: auto; max-width: 520px; padding: 40px; text-align: center; }
.sr-only { position: absolute; width: 1px; height: 1px; margin: -1px; padding: 0; overflow: hidden; clip: rect(0 0 0 0); border: 0; }
@media (max-width: 900px) {
  #view-slides { grid-template-columns: minmax(0, 1fr); grid-template-rows: minmax(0, 1fr) auto; }
  .filmstrip { order: 2; flex-direction: row; overflow-x: auto; border-right: 0; border-top: 1px solid var(--border); }
  .film-item { width: 150px; flex: none; }
  .side { display: none; }
  .presenter { grid-template-columns: minmax(0, 1fr); grid-template-rows: auto auto auto; overflow-y: auto; }
  .p-stage-wrap { aspect-ratio: var(--aspect); flex: none; }
  .topbar { flex-wrap: wrap; }
}
`;
var BODY = `
<header class="topbar">
  <div class="deck">
    <div class="deck-title" id="deck-title"></div>
    <div class="deck-meta" id="deck-meta"></div>
  </div>
  <div class="tabs" role="tablist" aria-label="View">
    <button type="button" role="tab" data-view="slides" title="Slide by slide, with the notes (S)">Slides</button>
    <button type="button" role="tab" data-view="grid" title="All the slides at once (G)">Grid</button>
  </div>
  <div class="actions">
    <button type="button" class="btn primary" id="btn-present" data-icon="play" title="Slide show from the first slide (F5)">Present</button>
    <button type="button" class="btn" id="btn-present-here" title="Slide show from the current slide (Shift+F5)">From current</button>
    <button type="button" class="btn" id="btn-presenter" data-icon="presenter" title="Presenter view: notes, next slide and timer (P)">Presenter</button>
    <button type="button" class="btn icon" id="btn-theme" data-icon="theme" title="Theme"></button>
    <button type="button" class="btn icon" id="btn-settings" data-icon="gear" title="Settings" aria-label="Settings"></button>
    <button type="button" class="btn icon" id="btn-help" data-icon="help" title="Keyboard shortcuts (?)" aria-label="Keyboard shortcuts"></button>
  </div>
</header>

<main class="view" id="view-slides">
  <nav class="filmstrip" id="filmstrip" aria-label="Slides"></nav>
  <section class="stage-col" aria-label="Current slide">
    <div class="stage" id="main-stage" tabindex="-1" title="Click for the next slide"></div>
    <div class="stage-bar">
      <button type="button" class="btn icon" data-act="first" data-icon="first" title="First slide (Home)" aria-label="First slide"></button>
      <button type="button" class="btn icon" data-act="prev" data-icon="prev" title="Previous slide (Left)" aria-label="Previous slide"></button>
      <span class="counter" id="main-counter"></span>
      <button type="button" class="btn icon" data-act="next" data-icon="next" title="Next slide (Right or Space)" aria-label="Next slide"></button>
      <button type="button" class="btn icon" data-act="last" data-icon="last" title="Last slide (End)" aria-label="Last slide"></button>
      <div class="flags" id="main-flags"></div>
      <span class="spacer"></span>
      <button type="button" class="btn icon" id="btn-replay" data-icon="replay" title="Play this slide's transition again (R)" aria-label="Replay the transition"></button>
    </div>
  </section>
  <aside class="side" id="side" aria-label="Slide details"></aside>
</main>

<main class="view" id="view-grid" hidden>
  <div class="toolbar">
    <label>Size <input type="range" id="grid-size" min="120" max="520" step="10"></label>
    <span class="spacer"></span>
    <span class="muted" id="grid-summary"></span>
  </div>
  <div class="grid-scroll"><div class="grid" id="grid"></div></div>
</main>

<div class="presenter" id="presenter" hidden>
  <section class="p-main" aria-label="Current slide">
    <div class="p-head"><span>Current</span><span class="spacer"></span><span id="p-counter"></span></div>
    <div class="p-stage-wrap">
      <div class="stage" id="p-stage" tabindex="-1"></div>
      <div class="p-cover" id="p-cover" hidden></div>
      <div class="p-overlay" id="p-ended" hidden>End of slide show</div>
    </div>
  </section>
  <aside class="p-side" aria-label="Next slide and notes">
    <div class="p-head"><span>Next</span><span class="spacer"></span><span id="p-next-label"></span></div>
    <div class="p-next-wrap">
      <div class="stage" id="p-next"></div>
      <div class="p-overlay" id="p-next-end" hidden>End of slide show</div>
    </div>
    <div class="p-head">
      <span>Notes</span><span class="spacer"></span>
      <button type="button" class="btn small" id="p-font-down" title="Smaller notes" aria-label="Smaller notes">A-</button>
      <button type="button" class="btn small" id="p-font-up" title="Larger notes" aria-label="Larger notes">A+</button>
    </div>
    <div class="p-notes" id="p-notes"></div>
  </aside>
  <footer class="p-bar">
    <button type="button" class="btn icon" data-act="prev" data-icon="prev" title="Previous (Left)" aria-label="Previous"></button>
    <button type="button" class="btn primary" data-act="next" data-icon="next" title="Next (Right or Space)">Next</button>
    <span class="timer" id="p-timer" title="Time since the presenter view opened">00:00:00</span>
    <button type="button" class="btn icon" id="p-pause" data-icon="pause" title="Pause or resume the timer" aria-label="Pause the timer" aria-pressed="false"></button>
    <button type="button" class="btn icon" id="p-reset" data-icon="replay" title="Restart the timer" aria-label="Restart the timer"></button>
    <span class="clock" id="p-clock"></span>
    <span class="spacer"></span>
    <button type="button" class="btn" id="p-black" title="Black screen (B)" aria-pressed="false">Black</button>
    <button type="button" class="btn" id="p-white" title="White screen (W)" aria-pressed="false">White</button>
    <button type="button" class="btn" id="p-audience" data-icon="window" title="Open the slides in a second window for the audience; this view drives it">Audience window</button>
    <button type="button" class="btn" id="p-exit" data-icon="close" title="Leave the presenter view (Esc)">Exit</button>
  </footer>
</div>

<div class="show" id="show" hidden>
  <div class="stage" id="show-stage" tabindex="-1"></div>
  <div class="progress" id="show-progress"></div>
  <div class="cover" id="show-cover" hidden></div>
  <div class="jump" id="show-jump" hidden></div>
  <div class="hud" id="show-hud">
    <button type="button" class="btn icon" data-act="prev" data-icon="prev" title="Previous (Left)" aria-label="Previous"></button>
    <span class="counter" id="show-counter"></span>
    <button type="button" class="btn icon" data-act="next" data-icon="next" title="Next (Right or Space)" aria-label="Next"></button>
    <button type="button" class="btn icon" id="show-auto" data-icon="clock" title="Pause or resume auto-advance (A)" aria-label="Auto-advance" aria-pressed="false"></button>
    <button type="button" class="btn icon" id="show-fullscreen" data-icon="fullscreen" title="Full screen (F)" aria-label="Full screen"></button>
    <button type="button" class="btn icon" id="show-help" data-icon="help" title="Keyboard shortcuts (?)" aria-label="Keyboard shortcuts"></button>
    <button type="button" class="btn icon" id="show-exit" data-icon="close" title="End the show (Esc)" aria-label="End the show"></button>
  </div>
</div>

<dialog id="dlg-settings" aria-labelledby="dlg-settings-title">
  <form method="dialog">
    <div class="dlg-head">
      <h2 id="dlg-settings-title">Settings</h2>
      <button class="btn icon" value="close" data-icon="close" aria-label="Close"></button>
    </div>
    <div class="dlg-body">
      <label class="field"><span>Theme</span>
        <select id="set-theme">
          <option value="auto">Match the system</option>
          <option value="light">Light</option>
          <option value="dark">Dark</option>
        </select>
      </label>
      <h3>Slide show</h3>
      <label class="field"><span>Motion</span>
        <select id="set-motion">
          <option value="auto">Match the system</option>
          <option value="full">Play transitions</option>
          <option value="reduced">Reduce motion: cut between slides</option>
        </select>
      </label>
      <label class="check"><input type="checkbox" id="set-loop"> <span>Loop: start again after the last slide</span></label>
      <label class="check"><input type="checkbox" id="set-progress"> <span>Show a progress bar</span></label>
      <label class="field"><span>Advance automatically every (seconds, 0 is off)</span><input type="number" id="set-auto" min="0" max="3600" step="1"></label>
    </div>
  </form>
</dialog>

<dialog id="dlg-help" aria-labelledby="dlg-help-title">
  <form method="dialog">
    <div class="dlg-head">
      <h2 id="dlg-help-title">Keyboard shortcuts</h2>
      <button class="btn icon" value="close" data-icon="close" aria-label="Close"></button>
    </div>
    <div class="dlg-body">
      <h3>Slide show and presenter view</h3>
      <table class="keys"><tbody>
        <tr><td><kbd>Right</kbd><kbd>Down</kbd><kbd>Space</kbd><kbd>Enter</kbd><kbd>N</kbd> or a click</td><td>Next slide (during a transition: finish it)</td></tr>
        <tr><td><kbd>Left</kbd><kbd>Up</kbd><kbd>Backspace</kbd><kbd>P</kbd></td><td>Previous slide</td></tr>
        <tr><td><kbd>Home</kbd> / <kbd>End</kbd></td><td>First / last slide</td></tr>
        <tr><td>number, then <kbd>Enter</kbd></td><td>Go to that slide</td></tr>
        <tr><td><kbd>B</kbd> or <kbd>.</kbd></td><td>Black screen</td></tr>
        <tr><td><kbd>W</kbd> or <kbd>,</kbd></td><td>White screen</td></tr>
        <tr><td><kbd>R</kbd></td><td>Play the slide's transition again</td></tr>
        <tr><td><kbd>A</kbd></td><td>Pause or resume auto-advance</td></tr>
        <tr><td><kbd>F</kbd></td><td>Full screen</td></tr>
        <tr><td><kbd>Esc</kbd></td><td>End the show</td></tr>
      </tbody></table>
      <h3>Slides and grid</h3>
      <table class="keys"><tbody>
        <tr><td><kbd>Right</kbd><kbd>Space</kbd> / <kbd>Left</kbd></td><td>Next / previous slide</td></tr>
        <tr><td><kbd>Home</kbd> / <kbd>End</kbd></td><td>First / last slide</td></tr>
        <tr><td><kbd>F5</kbd> / <kbd>Shift</kbd>+<kbd>F5</kbd></td><td>Present from the start / from here</td></tr>
        <tr><td><kbd>P</kbd></td><td>Presenter view</td></tr>
        <tr><td><kbd>S</kbd> <kbd>G</kbd></td><td>Slides or grid view</td></tr>
        <tr><td><kbd>R</kbd></td><td>Play the slide's transition again</td></tr>
        <tr><td><kbd>T</kbd></td><td>Switch theme</td></tr>
        <tr><td><kbd>?</kbd></td><td>This help</td></tr>
      </tbody></table>
      <p class="muted">A link like <code>#view=show&amp;slide=5</code> opens that view at that slide.</p>
    </div>
  </form>
</dialog>

<div class="toast" id="toast" role="status" aria-live="polite" hidden></div>
<div class="sr-only" id="slide-live" aria-live="polite" aria-atomic="true"></div>
<noscript><p class="fatal">This slide show needs JavaScript.</p></noscript>
`;
/** The page's script: the viewer, run with the transition engine. */
function buildScript() {
	return `(${String(openLyricHtmlSlideshowRuntime)})(${String(createOpenLyricTransitionEngine)});`;
}
/** `text` safe inside `<script>`: nothing in it can close the element. */
var toScriptText = (text) => text.replace(/<\/(script)/giu, "<\\/$1");
/**
* The deck `data` as one self-contained HTML page, as a string: the
* slideshow viewer, the deck's pictures and the transitions all in it.
*/
function buildOpenLyricPresentationHtml(data, options = {}) {
	const deck = buildOpenLyricHtmlDeck(data, options);
	const { translate } = options;
	const json = JSON.stringify(deck).replace(/</gu, "\\u003c");
	const lang = /^[A-Za-z]{2,8}(?:-[A-Za-z0-9]{1,8})*$/u.test(String(options.lang ?? "")) ? String(options.lang) : "en";
	const fontCss = String(options.fontCss ?? "").replace(/<\/?style/giu, "");
	const body = typeof translate === "function" ? mapMarkupWords(BODY, (text) => translateWith(translate, text)) : BODY;
	return `<!DOCTYPE html>
<html lang="${lang}">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="generator" content="Open Lyric">
<title>${escapeHtml(deck.title || translateWith(translate, "Slide show"))}</title>
${fontCss ? `<style>${fontCss}</style>\n` : ""}<style>${STYLE}</style>
</head>
<body>
<script id="ol-deck" type="application/json">${json}<\/script>
${body}
<script>${toScriptText(buildScript())}<\/script>
</body>
</html>
`;
}
//#endregion
//#region src/plugins/OpenLyric/preview/controller/pptx/zip.ts
/**
* The smallest ZIP writer a `.pptx` needs.
*
* An Office Open XML package is a plain ZIP archive, so writing one takes a
* local header per entry, one central-directory record per entry, and an
* end-of-central-directory record — no data descriptors (every size is known
* before the entry is written), no Zip64 (a song deck is far under 4GB), and
* no directory entries (PowerPoint reads the paths out of the names).
*
* Compression is raw DEFLATE through the platform's `CompressionStream`, which
* every browser this app supports has. Where it is missing — jsdom, an older
* WebView — entries are stored uncompressed instead: a bigger file, still a
* valid one, which is the right trade for an export that must not fail.
*/
var LOCAL_FILE_HEADER_SIGNATURE = 67324752;
var CENTRAL_DIRECTORY_SIGNATURE = 33639248;
var END_OF_CENTRAL_DIRECTORY_SIGNATURE = 101010256;
var ZIP_VERSION_NEEDED = 20;
var ZIP_UTF8_NAME_FLAG = 2048;
var COMPRESSION_METHOD_STORE = 0;
var COMPRESSION_METHOD_DEFLATE = 8;
var DOS_TIME = 0;
var DOS_DATE = 33;
var crcTable = null;
function getCrcTable() {
	if (crcTable) return crcTable;
	const table = /* @__PURE__ */ new Uint32Array(256);
	for (let index = 0; index < 256; index += 1) {
		let value = index;
		for (let bit = 0; bit < 8; bit += 1) value = value & 1 ? 3988292384 ^ value >>> 1 : value >>> 1;
		table[index] = value >>> 0;
	}
	crcTable = table;
	return table;
}
function crc32(bytes) {
	const table = getCrcTable();
	let crc = 4294967295;
	for (let index = 0; index < bytes.length; index += 1) crc = table[(crc ^ bytes[index]) & 255] ^ crc >>> 8;
	return (crc ^ 4294967295) >>> 0;
}
async function deflateRaw(bytes) {
	const CompressionStreamConstructor = globalThis.CompressionStream;
	if (typeof CompressionStreamConstructor !== "function") return null;
	try {
		const compressedStream = new Blob([bytes]).stream().pipeThrough(new CompressionStreamConstructor("deflate-raw"));
		return new Uint8Array(await new Response(compressedStream).arrayBuffer());
	} catch (_error) {
		return null;
	}
}
function toBytes(data) {
	return typeof data === "string" ? new TextEncoder().encode(data) : data;
}
function buildLocalFileHeader(entry) {
	const header = new Uint8Array(30 + entry.nameBytes.length);
	const view = new DataView(header.buffer);
	view.setUint32(0, LOCAL_FILE_HEADER_SIGNATURE, true);
	view.setUint16(4, ZIP_VERSION_NEEDED, true);
	view.setUint16(6, ZIP_UTF8_NAME_FLAG, true);
	view.setUint16(8, entry.compressionMethod, true);
	view.setUint16(10, DOS_TIME, true);
	view.setUint16(12, DOS_DATE, true);
	view.setUint32(14, entry.crc, true);
	view.setUint32(18, entry.compressedData.length, true);
	view.setUint32(22, entry.uncompressedSize, true);
	view.setUint16(26, entry.nameBytes.length, true);
	view.setUint16(28, 0, true);
	header.set(entry.nameBytes, 30);
	return header;
}
function buildCentralDirectoryRecord(entry) {
	const record = new Uint8Array(46 + entry.nameBytes.length);
	const view = new DataView(record.buffer);
	view.setUint32(0, CENTRAL_DIRECTORY_SIGNATURE, true);
	view.setUint16(4, ZIP_VERSION_NEEDED, true);
	view.setUint16(6, ZIP_VERSION_NEEDED, true);
	view.setUint16(8, ZIP_UTF8_NAME_FLAG, true);
	view.setUint16(10, entry.compressionMethod, true);
	view.setUint16(12, DOS_TIME, true);
	view.setUint16(14, DOS_DATE, true);
	view.setUint32(16, entry.crc, true);
	view.setUint32(20, entry.compressedData.length, true);
	view.setUint32(24, entry.uncompressedSize, true);
	view.setUint16(28, entry.nameBytes.length, true);
	view.setUint16(30, 0, true);
	view.setUint16(32, 0, true);
	view.setUint16(34, 0, true);
	view.setUint16(36, 0, true);
	view.setUint32(38, 0, true);
	view.setUint32(42, entry.localHeaderOffset, true);
	record.set(entry.nameBytes, 46);
	return record;
}
function buildEndOfCentralDirectory(entryCount, centralDirectorySize, centralDirectoryOffset) {
	const record = /* @__PURE__ */ new Uint8Array(22);
	const view = new DataView(record.buffer);
	view.setUint32(0, END_OF_CENTRAL_DIRECTORY_SIGNATURE, true);
	view.setUint16(4, 0, true);
	view.setUint16(6, 0, true);
	view.setUint16(8, entryCount, true);
	view.setUint16(10, entryCount, true);
	view.setUint32(12, centralDirectorySize, true);
	view.setUint32(16, centralDirectoryOffset, true);
	view.setUint16(20, 0, true);
	return record;
}
/**
* Pack `entries` into a ZIP archive. `isCompressed` asks for DEFLATE; entries
* that do not shrink (an already-compressed PNG) are stored either way, since
* a deflate stream longer than its input is only a bigger file.
*/
async function createZipBlob(entries, { isCompressed = true, mimeType = "application/zip" } = {}) {
	const stagedEntries = [];
	const parts = [];
	let offset = 0;
	for (const entry of entries) {
		const bytes = toBytes(entry.data);
		const deflated = isCompressed ? await deflateRaw(bytes) : null;
		const isDeflateSmaller = Boolean(deflated && deflated.length < bytes.length);
		const stagedEntry = {
			compressedData: isDeflateSmaller ? deflated : bytes,
			compressionMethod: isDeflateSmaller ? COMPRESSION_METHOD_DEFLATE : COMPRESSION_METHOD_STORE,
			crc: crc32(bytes),
			localHeaderOffset: offset,
			nameBytes: new TextEncoder().encode(entry.name),
			uncompressedSize: bytes.length
		};
		const localHeader = buildLocalFileHeader(stagedEntry);
		stagedEntries.push(stagedEntry);
		parts.push(localHeader, stagedEntry.compressedData);
		offset += localHeader.length + stagedEntry.compressedData.length;
	}
	const centralDirectoryOffset = offset;
	let centralDirectorySize = 0;
	for (const stagedEntry of stagedEntries) {
		const record = buildCentralDirectoryRecord(stagedEntry);
		parts.push(record);
		centralDirectorySize += record.length;
	}
	parts.push(buildEndOfCentralDirectory(stagedEntries.length, centralDirectorySize, centralDirectoryOffset));
	return new Blob(parts, { type: mimeType });
}
//#endregion
//#region src/plugins/OpenLyric/preview/controller/pptx/presentation.ts
/**
* A `.pptx` writer, small enough to read in one sitting.
*
* It covers exactly what the Open Lyric deck asks for — a 16:9 presentation
* whose slides carry a solid or picture background, text boxes, full-bleed pictures,
* plain-text speaker notes, a transition into the slide, and a picture coming
* on or leaving as the slide starts (the lyrics moving alone) — and nothing
* else: no charts, no tables, no animation on a click. That is the whole
* reason it exists in place of a general-purpose library.
*
* The shape of the API deliberately mirrors the handful of calls the exports
* already made (`addSlide`, `slide.addText`, `slide.addImage`, `write`), so the
* two call sites read the same as before.
*
* Geometry is in inches, type in points, colours as bare `RRGGBB` — the units
* PowerPoint's own UI uses. They are converted to EMU (914400 per inch) and
* hundredths of a point on the way out, which is what the file format wants.
*/
var EMU_PER_INCH = 914400;
var EMU_PER_POINT = 12700;
var SLIDE_WIDTH_EMU = 12192e3;
var SLIDE_HEIGHT_EMU = 6858e3;
var NOTES_WIDTH_EMU = 6858e3;
var NOTES_HEIGHT_EMU = 9144e3;
var PPTX_MIME_TYPE = "application/vnd.openxmlformats-officedocument.presentationml.presentation";
var XML_DECLARATION = "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"yes\"?>";
var DRAWING_NS = "http://schemas.openxmlformats.org/drawingml/2006/main";
var PRESENTATION_NS = "http://schemas.openxmlformats.org/presentationml/2006/main";
var RELATIONSHIP_NS = "http://schemas.openxmlformats.org/officeDocument/2006/relationships";
var PACKAGE_RELATIONSHIP_NS = "http://schemas.openxmlformats.org/package/2006/relationships";
var FIRST_SLIDE_ID = 256;
var NOTES_MASTER_CONTENT_TYPE = "application/vnd.openxmlformats-officedocument.presentationml.notesMaster+xml";
var NOTES_SLIDE_CONTENT_TYPE = "application/vnd.openxmlformats-officedocument.presentationml.notesSlide+xml";
var THEME_CONTENT_TYPE = "application/vnd.openxmlformats-officedocument.theme+xml";
var MARKUP_COMPATIBILITY_NS = "http://schemas.openxmlformats.org/markup-compatibility/2006";
var TRANSITION_NAMESPACES = {
	p14: "http://schemas.microsoft.com/office/powerpoint/2010/main",
	p15: "http://schemas.microsoft.com/office/powerpoint/2012/main",
	p159: "http://schemas.microsoft.com/office/powerpoint/2015/09/main"
};
/** The attributes direction `direction` sets on a transition's element. */
function toDirectionAttributes(spec, direction) {
	if (!direction) return {};
	if (spec.directions === "split") {
		const [orient, dir] = direction.split("-");
		return {
			orient,
			dir
		};
	}
	return { dir: direction };
}
/**
* The `<p:transition>` element — it follows `<p:clrMapOvr>` in a slide —
* written the way PowerPoint 2010 and later write theirs: an
* `mc:AlternateContent` whose choice holds the transition with its length in
* `p14:dur` (needing `p14`, or the namespace of a newer one: `p15` for the
* 2013 presets, `p159` for Morph), and whose fallback is a fade. A viewer
* that does not know a transition — Open Worship's converter included —
* takes the fade rather than cutting.
*
* Morph matches the shapes the two slides share — a picture of one name and
* one image holds still — and fades the others out and in.
*/
function buildTransitionXml(transition) {
	const spec = transition ? getOpenLyricPowerPointTransitionSpec(transition.type) : null;
	if (!transition || !spec) return "";
	const speed = transition.speed ?? "med";
	const prefix = spec.tag.split(":")[0];
	const attributes = {
		...spec.attributes,
		...toDirectionAttributes(spec, resolveOpenLyricPowerPointTransitionDirection(spec.id, transition.direction))
	};
	const effect = `<${spec.tag}${Object.entries(attributes).map(([name, value]) => ` ${name}="${escapeXml(value)}"`).join("")}/>`;
	const extraNamespace = prefix === "p" || prefix === "p14" ? "" : ` xmlns:${prefix}="${TRANSITION_NAMESPACES[prefix]}"`;
	const duration = getOpenLyricPowerPointTransitionDurationMs(spec.id, speed);
	const fallback = spec.id === "cut" ? "<p:cut/>" : "<p:fade/>";
	return `<mc:AlternateContent xmlns:mc="${MARKUP_COMPATIBILITY_NS}"><mc:Choice xmlns:p14="${TRANSITION_NAMESPACES.p14}"${extraNamespace} Requires="${prefix === "p" ? "p14" : prefix}"><p:transition spd="${speed}" p14:dur="${duration}">${effect}</p:transition></mc:Choice><mc:Fallback><p:transition spd="${speed}">${fallback}</p:transition></mc:Fallback></mc:AlternateContent>`;
}
/** Fly In's subtype (the side it comes from) and its start, by direction. */
var FLY_FROM = {
	u: [
		4,
		"#ppt_x",
		"1+#ppt_h/2"
	],
	d: [
		1,
		"#ppt_x",
		"0-#ppt_h/2"
	],
	l: [
		2,
		"1+#ppt_w/2",
		"#ppt_y"
	],
	r: [
		8,
		"0-#ppt_w/2",
		"#ppt_y"
	],
	lu: [
		6,
		"1+#ppt_w/2",
		"1+#ppt_h/2"
	],
	ru: [
		12,
		"0-#ppt_w/2",
		"1+#ppt_h/2"
	],
	ld: [
		3,
		"1+#ppt_w/2",
		"0-#ppt_h/2"
	],
	rd: [
		9,
		"0-#ppt_w/2",
		"0-#ppt_h/2"
	]
};
var FILTER_PRESETS = {
	fade: { "": [
		10,
		0,
		"fade"
	] },
	wipe: {
		r: [
			22,
			8,
			"wipe(right)"
		],
		l: [
			22,
			2,
			"wipe(left)"
		],
		u: [
			22,
			4,
			"wipe(up)"
		],
		d: [
			22,
			1,
			"wipe(down)"
		]
	},
	split: {
		"vert-out": [
			16,
			42,
			"barn(outVertical)"
		],
		"vert-in": [
			16,
			37,
			"barn(inVertical)"
		],
		"horz-out": [
			16,
			26,
			"barn(outHorizontal)"
		],
		"horz-in": [
			16,
			21,
			"barn(inHorizontal)"
		]
	},
	circle: { "": [
		6,
		32,
		"circle(out)"
	] },
	diamond: { "": [
		8,
		32,
		"diamond(out)"
	] },
	plus: { "": [
		13,
		32,
		"plus(out)"
	] },
	randomBars: {
		vert: [
			14,
			5,
			"randombar(vertical)"
		],
		horz: [
			14,
			10,
			"randombar(horizontal)"
		]
	},
	clock: { "": [
		21,
		1,
		"wheel(1)"
	] },
	wheel: { "": [
		21,
		4,
		"wheel(4)"
	] },
	wedge: { "": [
		20,
		0,
		"wedge"
	] },
	dissolve: { "": [
		9,
		0,
		"dissolve"
	] },
	checkerboard: {
		horz: [
			5,
			10,
			"checkerboard(across)"
		],
		vert: [
			5,
			5,
			"checkerboard(down)"
		]
	},
	blinds: {
		horz: [
			3,
			10,
			"blinds(horizontal)"
		],
		vert: [
			3,
			5,
			"blinds(vertical)"
		]
	},
	strips: {
		rd: [
			18,
			6,
			"strips(downRight)"
		],
		ld: [
			18,
			12,
			"strips(downLeft)"
		],
		ru: [
			18,
			3,
			"strips(upRight)"
		],
		lu: [
			18,
			9,
			"strips(upLeft)"
		]
	}
};
/** The preset text effect `effect` plays in `direction`; Fade for one the writer does not know. */
function getTextEffectPreset(effect, direction) {
	const resolved = resolveOpenLyricPowerPointTextDirection(effect, direction);
	if (effect === "fly") {
		const [subtype, x, y] = FLY_FROM[resolved] ?? FLY_FROM.u;
		return {
			presetId: 2,
			subtype,
			from: [x, y]
		};
	}
	if (effect === "zoom") return {
		presetId: 53,
		subtype: 16,
		isZoom: true
	};
	const [presetId, subtype, filter] = FILTER_PRESETS[effect]?.[resolved] ?? FILTER_PRESETS.fade[""];
	return {
		presetId,
		subtype,
		filter
	};
}
/**
* One picture's entrance or exit: an effect node (`presetClass` `entr` or
* `exit`) with its behaviours, as PowerPoint writes them. An entrance first
* makes the picture visible; an exit plays the same behaviours backwards
* (`transition="out"`, the flight away to where it came from) and hides it
* as it ends. `nextId` numbers the time nodes in document order.
*/
function buildAnimationEffectXml(spid, animation, nodeType, nextId) {
	const isIn = animation.type !== "out";
	const duration = Math.max(1, Math.round(Number(animation.durationMs) || 0));
	const preset = getTextEffectPreset(animation.effect, animation.direction);
	const effectId = nextId();
	const target = `<p:tgtEl><p:spTgt spid="${spid}"/></p:tgtEl>`;
	const visibility = (value, delay) => `<p:set><p:cBhvr><p:cTn id="${nextId()}" dur="1" fill="hold"><p:stCondLst><p:cond delay="${delay}"/></p:stCondLst></p:cTn>${target}<p:attrNameLst><p:attrName>style.visibility</p:attrName></p:attrNameLst></p:cBhvr><p:to><p:strVal val="${value}"/></p:to></p:set>`;
	const anim = (attribute, from, to) => `<p:anim calcmode="lin" valueType="num"><p:cBhvr additive="base"><p:cTn id="${nextId()}" dur="${duration}" fill="hold"/>${target}<p:attrNameLst><p:attrName>${attribute}</p:attrName></p:attrNameLst></p:cBhvr><p:tavLst><p:tav tm="0"><p:val><p:strVal val="${escapeXml(from)}"/></p:val></p:tav><p:tav tm="100000"><p:val><p:strVal val="${escapeXml(to)}"/></p:val></p:tav></p:tavLst></p:anim>`;
	const filter = (name) => `<p:animEffect transition="${isIn ? "in" : "out"}" filter="${escapeXml(name)}"><p:cBhvr><p:cTn id="${nextId()}" dur="${duration}"/>${target}</p:cBhvr></p:animEffect>`;
	const own = (formula) => formula.replace(/#/g, "");
	/** From `start` to the picture's place coming on; the other way leaving. */
	const move = (attribute, start, place) => isIn ? anim(attribute, start, place) : anim(attribute, own(place), own(start));
	const parts = [];
	if (isIn) parts.push(visibility("visible", 0));
	if (preset.from) parts.push(move("ppt_x", preset.from[0], "#ppt_x"), move("ppt_y", preset.from[1], "#ppt_y"));
	else if (preset.isZoom) parts.push(move("ppt_w", "0", "#ppt_w"), move("ppt_h", "0", "#ppt_h"), filter("fade"));
	else parts.push(filter(preset.filter ?? "fade"));
	if (!isIn) parts.push(visibility("hidden", duration - 1));
	return `<p:par><p:cTn id="${effectId}" presetID="${preset.presetId}" presetClass="${isIn ? "entr" : "exit"}" presetSubtype="${preset.subtype}" fill="hold" grpId="0" nodeType="${nodeType}"><p:stCondLst><p:cond delay="0"/></p:stCondLst><p:childTnLst>${parts.join("")}</p:childTnLst></p:cTn></p:par>`;
}
/**
* The slide's `<p:timing>` — it follows `<p:transition>` — for its pictures
* that come on or leave, or `''` for none. One step of the main sequence
* that starts with the slide (`onBegin` of the sequence, PowerPoint's *With
* Previous* on the first effect), so no click is asked for: the pictures
* leaving all together, then (*After Previous*) the ones coming on. Showing
* the slide again from later in the show — going back — shows it as it ends.
*/
function buildTimingXml(builds) {
	if (!builds.length) return "";
	let lastId = 2;
	const nextId = () => {
		lastId += 1;
		return lastId;
	};
	const exits = builds.filter((build) => build.animation.type === "out");
	const entrances = builds.filter((build) => build.animation.type !== "out");
	const exitLength = Math.max(0, ...exits.map((build) => Math.max(1, Math.round(Number(build.animation.durationMs) || 0))));
	const groups = [{
		delay: 0,
		builds: exits
	}, {
		delay: exits.length ? exitLength : 0,
		builds: entrances
	}].filter((group) => group.builds.length);
	return `<p:timing><p:tnLst><p:par><p:cTn id="1" dur="indefinite" restart="never" nodeType="tmRoot"><p:childTnLst><p:seq concurrent="1" nextAc="seek"><p:cTn id="2" dur="indefinite" nodeType="mainSeq"><p:childTnLst><p:par><p:cTn id="${nextId()}" fill="hold"><p:stCondLst><p:cond delay="indefinite"/><p:cond evt="onBegin" delay="0"><p:tn val="2"/></p:cond></p:stCondLst><p:childTnLst>${groups.map((group, groupIndex) => {
		const groupId = nextId();
		const effects = group.builds.map((build, index) => buildAnimationEffectXml(build.spid, build.animation, groupIndex > 0 && index === 0 ? "afterEffect" : "withEffect", nextId)).join("");
		return `<p:par><p:cTn id="${groupId}" fill="hold"><p:stCondLst><p:cond delay="${group.delay}"/></p:stCondLst><p:childTnLst>${effects}</p:childTnLst></p:cTn></p:par>`;
	}).join("")}</p:childTnLst></p:cTn></p:par></p:childTnLst></p:cTn><p:prevCondLst><p:cond evt="onPrev" delay="0"><p:tgtEl><p:sldTgt/></p:tgtEl></p:cond></p:prevCondLst><p:nextCondLst><p:cond evt="onNext" delay="0"><p:tgtEl><p:sldTgt/></p:tgtEl></p:cond></p:nextCondLst></p:seq></p:childTnLst></p:cTn></p:par></p:tnLst></p:timing>`;
}
/** PowerPoint's *Mark as decorative* (Office 2019 and later). */
var PPTX_DECORATIVE_EXTENSION_URI = "{C183D7F6-B498-43B3-948B-1728B52AA6E4}";
var PPTX_DECORATIVE_NAMESPACE = "http://schemas.microsoft.com/office/drawing/2017/decorative";
/**
* XML 1.0 can spell tab, newline and carriage return, and nothing else below
* `0x20`. A stray control character makes the whole package unreadable rather
* than the one run it sits in, so they are dropped before anything else.
*/
function stripInvalidXmlCharacters(text) {
	let output = "";
	for (const character of text) {
		const code = character.codePointAt(0) ?? 0;
		if (code === 9 || code === 10 || code === 13 || code >= 32) output += character;
	}
	return output;
}
function escapeXml(value) {
	return stripInvalidXmlCharacters(String(value ?? "")).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");
}
/** `RRGGBB` from `#RRGGBB`, `RRGGBB`, or a fallback when it is neither. */
function normalizeColor(color, fallback = "000000") {
	const normalized = String(color ?? "").trim().replace(/^#/, "").toUpperCase();
	return /^[0-9A-F]{6}$/.test(normalized) ? normalized : fallback;
}
/** Inches (or a `'50%'` share of `total`) as EMU. */
function toEmu(value, total, fallback = 0) {
	if (typeof value === "string" && value.trim().endsWith("%")) {
		const percent = Number.parseFloat(value);
		return Number.isFinite(percent) ? Math.round(percent / 100 * total) : fallback;
	}
	const inches = Number(value);
	return Number.isFinite(inches) ? Math.round(inches * EMU_PER_INCH) : fallback;
}
function resolveMargins(margin) {
	const asPoints = (value) => {
		const points = Number(value);
		return Number.isFinite(points) && points > 0 ? Math.round(points * EMU_PER_POINT) : 0;
	};
	if (Array.isArray(margin)) {
		const [left = 0, right = 0, bottom = 0, top = 0] = margin;
		return {
			left: asPoints(left),
			right: asPoints(right),
			bottom: asPoints(bottom),
			top: asPoints(top)
		};
	}
	const uniform = asPoints(margin);
	return {
		left: uniform,
		right: uniform,
		bottom: uniform,
		top: uniform
	};
}
function decodeDataUri(dataUri) {
	const text = String(dataUri ?? "");
	const mimeMatch = /^data:image\/([a-z0-9+.-]+);/i.exec(text);
	const base64 = text.slice(text.indexOf("base64,") + 7);
	const binary = globalThis.atob(base64);
	const bytes = new Uint8Array(binary.length);
	for (let index = 0; index < binary.length; index += 1) bytes[index] = binary.charCodeAt(index);
	const rawExtension = (mimeMatch?.[1] ?? "png").toLowerCase();
	return {
		bytes,
		extension: rawExtension === "jpg" ? "jpeg" : rawExtension
	};
}
function buildRelationships(relationships) {
	return `${XML_DECLARATION}<Relationships xmlns="${PACKAGE_RELATIONSHIP_NS}">${relationships.map(({ id, type, target }) => `<Relationship Id="${id}" Type="${type}" Target="${escapeXml(target)}"/>`).join("")}</Relationships>`;
}
var PptxSlide = class {
	/** Default run colour for text that names none. */
	color = "";
	/** Speaker notes, plain text; each line a paragraph. */
	notes = "";
	/**
	* How the slide comes on; `null` follows the deck's
	* {@link PptxPresentation.transition}, and `false` cuts in, whatever the
	* deck's — for a slide whose pictures come on by themselves.
	*/
	transition = null;
	shapes = [];
	builds = [];
	shapeData = [];
	imageRelationshipIds = [];
	addMedia;
	slideBackground = null;
	backgroundRelationshipId = "";
	constructor(addMedia) {
		this.addMedia = addMedia;
	}
	/** What is on the slide, in the order it was added. */
	get elements() {
		return this.shapeData;
	}
	/** What fills the whole slide behind its shapes; see {@link SlideBackground}. */
	get background() {
		return this.slideBackground;
	}
	set background(background) {
		this.slideBackground = background;
		this.backgroundRelationshipId = background?.data ? this.addMedia(background.data) : "";
	}
	addText(text, options = {}) {
		this.shapeData.push({
			kind: "text",
			text: String(text ?? ""),
			options: { ...options }
		});
		const paragraphs = String(text ?? "").split("\n");
		const margins = resolveMargins(options.margin);
		const alignment = {
			left: "l",
			center: "ctr",
			right: "r"
		}[options.align ?? "left"];
		const anchor = {
			top: "t",
			middle: "ctr",
			bottom: "b"
		}[options.valign ?? "top"];
		const runProperties = [
			`lang="en-US"`,
			`sz="${Math.round((Number(options.fontSize) || 18) * 100)}"`,
			options.bold ? "b=\"1\"" : "",
			"dirty=\"0\""
		].filter(Boolean).join(" ");
		const runColor = normalizeColor(options.color || this.color, this.color ? normalizeColor(this.color) : "000000");
		const fontFace = String(options.fontFace ?? "").trim();
		const typeface = fontFace ? `<a:latin typeface="${escapeXml(fontFace)}"/><a:cs typeface="${escapeXml(fontFace)}"/>` : "";
		const body = paragraphs.map((paragraph) => {
			const run = paragraph ? `<a:r><a:rPr ${runProperties}><a:solidFill><a:srgbClr val="${runColor}"/></a:solidFill>${typeface}</a:rPr><a:t>${escapeXml(paragraph)}</a:t></a:r>` : `<a:endParaRPr ${runProperties}/>`;
			return `<a:p><a:pPr algn="${alignment}"/>${run}</a:p>`;
		}).join("");
		const fillColor = options.fill?.color;
		const fill = fillColor ? `<a:solidFill><a:srgbClr val="${normalizeColor(fillColor)}"/></a:solidFill>` : "<a:noFill/>";
		const outline = options.line?.color ? `<a:ln w="${Math.round((Number(options.line.width) || 1) * EMU_PER_POINT)}"><a:solidFill><a:srgbClr val="${normalizeColor(options.line.color)}"/></a:solidFill></a:ln>` : "";
		const autofit = options.fit === "shrink" ? "<a:normAutofit/>" : "<a:spAutoFit/>";
		const index = this.shapes.length + 2;
		this.shapes.push(`<p:sp><p:nvSpPr><p:cNvPr id="${index}" name="Text ${index}"/><p:cNvSpPr txBox="1"/><p:nvPr/></p:nvSpPr><p:spPr>${this.buildTransform(options)}<a:prstGeom prst="rect"><a:avLst/></a:prstGeom>${fill}${outline}</p:spPr><p:txBody><a:bodyPr lIns="${margins.left}" tIns="${margins.top}" rIns="${margins.right}" bIns="${margins.bottom}" anchor="${anchor}" wrap="square">${autofit}</a:bodyPr><a:lstStyle/>${body}</p:txBody></p:sp>`);
	}
	addImage(options) {
		this.shapeData.push({
			kind: "image",
			options: { ...options }
		});
		const relationshipId = this.addMedia(options.data);
		const index = this.shapes.length + 2;
		const name = escapeXml(options.name?.trim() || `Image ${index}`);
		const description = String(options.description ?? "").trim();
		const descr = description ? ` descr="${escapeXml(description).replace(/\r\n?|\n/g, "&#10;")}"` : "";
		const decorative = !description && options.isDecorative ? `<a:extLst><a:ext uri="${PPTX_DECORATIVE_EXTENSION_URI}"><adec:decorative xmlns:adec="${PPTX_DECORATIVE_NAMESPACE}" val="1"/></a:ext></a:extLst>` : "";
		const nonVisualProperties = decorative ? `<p:cNvPr id="${index}" name="${name}"${descr}>${decorative}</p:cNvPr>` : `<p:cNvPr id="${index}" name="${name}"${descr}/>`;
		this.imageRelationshipIds.push(relationshipId);
		if (options.animation) this.builds.push({
			spid: index,
			animation: { ...options.animation }
		});
		this.shapes.push(`<p:pic><p:nvPicPr>${nonVisualProperties}<p:cNvPicPr><a:picLocks noChangeAspect="1"/></p:cNvPicPr><p:nvPr/></p:nvPicPr><p:blipFill><a:blip r:embed="${relationshipId}"/><a:stretch><a:fillRect/></a:stretch></p:blipFill><p:spPr>${this.buildTransform(options)}<a:prstGeom prst="rect"><a:avLst/></a:prstGeom></p:spPr></p:pic>`);
	}
	toXml(deckTransition = null) {
		return `${XML_DECLARATION}<p:sld xmlns:a="${DRAWING_NS}" xmlns:r="${RELATIONSHIP_NS}" xmlns:p="${PRESENTATION_NS}"><p:cSld>${this.buildBackgroundXml()}<p:spTree><p:nvGrpSpPr><p:cNvPr id="1" name=""/><p:cNvGrpSpPr/><p:nvPr/></p:nvGrpSpPr><p:grpSpPr><a:xfrm><a:off x="0" y="0"/><a:ext cx="0" cy="0"/><a:chOff x="0" y="0"/><a:chExt cx="0" cy="0"/></a:xfrm></p:grpSpPr>${this.shapes.join("")}</p:spTree></p:cSld><p:clrMapOvr><a:masterClrMapping/></p:clrMapOvr>${this.transition === false ? "" : buildTransitionXml(this.transition ?? deckTransition)}${buildTimingXml(this.builds)}</p:sld>`;
	}
	/** The `<p:bg>` element, or `''` for a slide that names no background. */
	buildBackgroundXml() {
		if (this.backgroundRelationshipId) return `<p:bg><p:bgPr><a:blipFill dpi="0" rotWithShape="1"><a:blip r:embed="${this.backgroundRelationshipId}"/><a:srcRect/><a:stretch><a:fillRect/></a:stretch></a:blipFill><a:effectLst/></p:bgPr></p:bg>`;
		const color = this.slideBackground?.color;
		return color ? `<p:bg><p:bgPr><a:solidFill><a:srgbClr val="${normalizeColor(color)}"/></a:solidFill><a:effectLst/></p:bgPr></p:bg>` : "";
	}
	buildTransform(box) {
		return `<a:xfrm><a:off x="${toEmu(box.x, SLIDE_WIDTH_EMU)}" y="${toEmu(box.y, SLIDE_HEIGHT_EMU)}"/><a:ext cx="${toEmu(box.w, SLIDE_WIDTH_EMU, SLIDE_WIDTH_EMU)}" cy="${toEmu(box.h, SLIDE_HEIGHT_EMU, SLIDE_HEIGHT_EMU)}"/></a:xfrm>`;
	}
};
var PptxPresentation = class {
	/** How every slide comes on that names no transition of its own. */
	transition = null;
	slides = [];
	mediaParts = [];
	mediaIdsByData = /* @__PURE__ */ new Map();
	relationshipIdsBySlide = /* @__PURE__ */ new Map();
	/** How many slides the deck has so far. */
	get slideCount() {
		return this.slides.length;
	}
	addSlide() {
		const slide = new PptxSlide((dataUri) => this.registerMedia(slide, dataUri));
		this.slides.push(slide);
		this.relationshipIdsBySlide.set(slide, []);
		return slide;
	}
	/**
	* The deck as plain data: each slide's background, shapes, notes and the
	* transition into it (the slide's own, or the deck's) — what
	* `writeOpenLyricPresentationHtml` draws.
	*/
	toData() {
		return {
			width: SLIDE_WIDTH_EMU / EMU_PER_INCH,
			height: SLIDE_HEIGHT_EMU / EMU_PER_INCH,
			slides: this.slides.map((slide) => ({
				background: slide.background ? { ...slide.background } : null,
				color: slide.color,
				elements: slide.elements.map((element) => ({
					...element,
					options: { ...element.options }
				})),
				notes: slide.notes,
				transition: slide.transition === false ? null : slide.transition ?? this.transition
			}))
		};
	}
	/** The finished deck, as a `.pptx` blob ready to hand to a download. */
	async write({ compression = true } = {}) {
		return createZipBlob(this.buildParts(), {
			isCompressed: compression,
			mimeType: PPTX_MIME_TYPE
		});
	}
	registerMedia(slide, dataUri) {
		const key = String(dataUri ?? "");
		const existingName = this.mediaIdsByData.get(key);
		const slideRelationships = this.relationshipIdsBySlide.get(slide) ?? [];
		let name = existingName;
		if (!name) {
			const { bytes, extension } = decodeDataUri(key);
			name = `image${this.mediaParts.length + 1}.${extension}`;
			this.mediaParts.push({
				bytes,
				extension,
				name
			});
			this.mediaIdsByData.set(key, name);
		}
		slideRelationships.push(name);
		this.relationshipIdsBySlide.set(slide, slideRelationships);
		return `rId${slideRelationships.length + 1}`;
	}
	buildParts() {
		const slideNumbers = this.slides.map((_slide, index) => index + 1);
		const notedSlideNumbers = slideNumbers.filter((slideNumber) => this.slides[slideNumber - 1].notes.trim());
		const hasNotes = notedSlideNumbers.length > 0;
		const imageExtensions = new Set(this.mediaParts.map((mediaPart) => mediaPart.extension));
		const parts = [
			{
				name: "[Content_Types].xml",
				data: `${XML_DECLARATION}<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types"><Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/><Default Extension="xml" ContentType="application/xml"/>` + [...imageExtensions].map((extension) => `<Default Extension="${extension}" ContentType="image/${extension}"/>`).join("") + `<Override PartName="/ppt/presentation.xml" ContentType="${PPTX_MIME_TYPE}.main+xml"/><Override PartName="/ppt/slideMasters/slideMaster1.xml" ContentType="application/vnd.openxmlformats-officedocument.presentationml.slideMaster+xml"/><Override PartName="/ppt/slideLayouts/slideLayout1.xml" ContentType="application/vnd.openxmlformats-officedocument.presentationml.slideLayout+xml"/><Override PartName="/ppt/theme/theme1.xml" ContentType="${THEME_CONTENT_TYPE}"/>` + (hasNotes ? `<Override PartName="/ppt/notesMasters/notesMaster1.xml" ContentType="${NOTES_MASTER_CONTENT_TYPE}"/><Override PartName="/ppt/theme/theme2.xml" ContentType="${THEME_CONTENT_TYPE}"/>` + notedSlideNumbers.map((slideNumber) => `<Override PartName="/ppt/notesSlides/notesSlide${slideNumber}.xml" ContentType="${NOTES_SLIDE_CONTENT_TYPE}"/>`).join("") : "") + slideNumbers.map((slideNumber) => `<Override PartName="/ppt/slides/slide${slideNumber}.xml" ContentType="application/vnd.openxmlformats-officedocument.presentationml.slide+xml"/>`).join("") + `</Types>`
			},
			{
				name: "_rels/.rels",
				data: buildRelationships([{
					id: "rId1",
					type: `${RELATIONSHIP_NS}/officeDocument`,
					target: "ppt/presentation.xml"
				}])
			},
			{
				name: "ppt/presentation.xml",
				data: this.buildPresentationXml()
			},
			{
				name: "ppt/_rels/presentation.xml.rels",
				data: buildRelationships([
					{
						id: "rId1",
						type: `${RELATIONSHIP_NS}/slideMaster`,
						target: "slideMasters/slideMaster1.xml"
					},
					...slideNumbers.map((slideNumber) => ({
						id: `rId${slideNumber + 1}`,
						type: `${RELATIONSHIP_NS}/slide`,
						target: `slides/slide${slideNumber}.xml`
					})),
					{
						id: `rId${slideNumbers.length + 2}`,
						type: `${RELATIONSHIP_NS}/theme`,
						target: "theme/theme1.xml"
					},
					...hasNotes ? [{
						id: `rId${slideNumbers.length + 3}`,
						type: `${RELATIONSHIP_NS}/notesMaster`,
						target: "notesMasters/notesMaster1.xml"
					}] : []
				])
			},
			{
				name: "ppt/theme/theme1.xml",
				data: buildThemeXml()
			},
			{
				name: "ppt/slideMasters/slideMaster1.xml",
				data: buildSlideMasterXml()
			},
			{
				name: "ppt/slideMasters/_rels/slideMaster1.xml.rels",
				data: buildRelationships([{
					id: "rId1",
					type: `${RELATIONSHIP_NS}/slideLayout`,
					target: "../slideLayouts/slideLayout1.xml"
				}, {
					id: "rId2",
					type: `${RELATIONSHIP_NS}/theme`,
					target: "../theme/theme1.xml"
				}])
			},
			{
				name: "ppt/slideLayouts/slideLayout1.xml",
				data: buildSlideLayoutXml()
			},
			{
				name: "ppt/slideLayouts/_rels/slideLayout1.xml.rels",
				data: buildRelationships([{
					id: "rId1",
					type: `${RELATIONSHIP_NS}/slideMaster`,
					target: "../slideMasters/slideMaster1.xml"
				}])
			}
		];
		if (hasNotes) parts.push({
			name: "ppt/theme/theme2.xml",
			data: buildThemeXml()
		}, {
			name: "ppt/notesMasters/notesMaster1.xml",
			data: buildNotesMasterXml()
		}, {
			name: "ppt/notesMasters/_rels/notesMaster1.xml.rels",
			data: buildRelationships([{
				id: "rId1",
				type: `${RELATIONSHIP_NS}/theme`,
				target: "../theme/theme2.xml"
			}])
		});
		this.slides.forEach((slide, index) => {
			const slideNumber = index + 1;
			const imageNames = this.relationshipIdsBySlide.get(slide) ?? [];
			const hasSlideNotes = Boolean(slide.notes.trim());
			if (hasSlideNotes) parts.push({
				name: `ppt/notesSlides/notesSlide${slideNumber}.xml`,
				data: buildNotesSlideXml(slide.notes)
			}, {
				name: `ppt/notesSlides/_rels/notesSlide${slideNumber}.xml.rels`,
				data: buildRelationships([{
					id: "rId1",
					type: `${RELATIONSHIP_NS}/notesMaster`,
					target: "../notesMasters/notesMaster1.xml"
				}, {
					id: "rId2",
					type: `${RELATIONSHIP_NS}/slide`,
					target: `../slides/slide${slideNumber}.xml`
				}])
			});
			parts.push({
				name: `ppt/slides/slide${slideNumber}.xml`,
				data: slide.toXml(this.transition)
			}, {
				name: `ppt/slides/_rels/slide${slideNumber}.xml.rels`,
				data: buildRelationships([
					{
						id: "rId1",
						type: `${RELATIONSHIP_NS}/slideLayout`,
						target: "../slideLayouts/slideLayout1.xml"
					},
					...imageNames.map((imageName, imageIndex) => ({
						id: `rId${imageIndex + 2}`,
						type: `${RELATIONSHIP_NS}/image`,
						target: `../media/${imageName}`
					})),
					...hasSlideNotes ? [{
						id: `rId${imageNames.length + 2}`,
						type: `${RELATIONSHIP_NS}/notesSlide`,
						target: `../notesSlides/notesSlide${slideNumber}.xml`
					}] : []
				])
			});
		});
		for (const mediaPart of this.mediaParts) parts.push({
			name: `ppt/media/${mediaPart.name}`,
			data: mediaPart.bytes
		});
		return parts;
	}
	buildPresentationXml() {
		const slideIds = this.slides.map((_slide, index) => `<p:sldId id="${FIRST_SLIDE_ID + index}" r:id="rId${index + 2}"/>`).join("");
		return `${XML_DECLARATION}<p:presentation xmlns:a="${DRAWING_NS}" xmlns:r="${RELATIONSHIP_NS}" xmlns:p="${PRESENTATION_NS}" saveSubsetFonts="1"><p:sldMasterIdLst><p:sldMasterId id="2147483648" r:id="rId1"/></p:sldMasterIdLst>` + (this.slides.some((slide) => slide.notes.trim()) ? `<p:notesMasterIdLst><p:notesMasterId r:id="rId${this.slides.length + 3}"/></p:notesMasterIdLst>` : "") + `<p:sldIdLst>${slideIds}</p:sldIdLst><p:sldSz cx="${SLIDE_WIDTH_EMU}" cy="${SLIDE_HEIGHT_EMU}"/><p:notesSz cx="${NOTES_WIDTH_EMU}" cy="${NOTES_HEIGHT_EMU}"/></p:presentation>`;
	}
};
function buildEmptyShapeTree() {
	return "<p:spTree><p:nvGrpSpPr><p:cNvPr id=\"1\" name=\"\"/><p:cNvGrpSpPr/><p:nvPr/></p:nvGrpSpPr><p:grpSpPr><a:xfrm><a:off x=\"0\" y=\"0\"/><a:ext cx=\"0\" cy=\"0\"/><a:chOff x=\"0\" y=\"0\"/><a:chExt cx=\"0\" cy=\"0\"/></a:xfrm></p:grpSpPr></p:spTree>";
}
function buildSlideMasterXml() {
	return `${XML_DECLARATION}<p:sldMaster xmlns:a="${DRAWING_NS}" xmlns:r="${RELATIONSHIP_NS}" xmlns:p="${PRESENTATION_NS}"><p:cSld><p:bg><p:bgPr><a:solidFill><a:schemeClr val="lt1"/></a:solidFill><a:effectLst/></p:bgPr></p:bg>${buildEmptyShapeTree()}</p:cSld><p:clrMap bg1="lt1" tx1="dk1" bg2="lt2" tx2="dk2" accent1="accent1" accent2="accent2" accent3="accent3" accent4="accent4" accent5="accent5" accent6="accent6" hlink="hlink" folHlink="folHlink"/><p:sldLayoutIdLst><p:sldLayoutId id="2147483649" r:id="rId1"/></p:sldLayoutIdLst><p:txStyles><p:titleStyle/><p:bodyStyle/><p:otherStyle/></p:txStyles></p:sldMaster>`;
}
function buildSlideLayoutXml() {
	return `${XML_DECLARATION}<p:sldLayout xmlns:a="${DRAWING_NS}" xmlns:r="${RELATIONSHIP_NS}" xmlns:p="${PRESENTATION_NS}" type="blank" preserve="1"><p:cSld name="Blank">${buildEmptyShapeTree()}</p:cSld><p:clrMapOvr><a:masterClrMapping/></p:clrMapOvr></p:sldLayout>`;
}
/** A placeholder shape: `sldImg` (the slide's picture) or `body` (notes). */
function buildPlaceholder(id, name, placeholder, { transform = "", body = "" } = {}) {
	return `<p:sp><p:nvSpPr><p:cNvPr id="${id}" name="${name}"/><p:cNvSpPr>${placeholder === "sldImg" ? "<a:spLocks noGrp=\"1\" noRot=\"1\" noChangeAspect=\"1\"/>" : "<a:spLocks noGrp=\"1\"/>"}</p:cNvSpPr><p:nvPr>${placeholder}</p:nvPr></p:nvSpPr><p:spPr>${transform}${transform ? "<a:prstGeom prst=\"rect\"><a:avLst/></a:prstGeom>" : ""}</p:spPr>${body}</p:sp>`;
}
/**
* The notes master: where a notes page puts the slide's picture and the notes
* under it. The notes pages name the two placeholders and inherit the rest.
*/
function buildNotesMasterXml() {
	const margin = 685800;
	const width = NOTES_WIDTH_EMU - 2 * margin;
	const imageHeight = Math.round(width * SLIDE_HEIGHT_EMU / SLIDE_WIDTH_EMU);
	const imageTop = 1143e3;
	const bodyTop = 4686300;
	const bodyHeight = 3543300;
	const box = (y, height) => `<a:xfrm><a:off x="${margin}" y="${y}"/><a:ext cx="${width}" cy="${height}"/></a:xfrm>`;
	const level = (index) => `<a:lvl${index}pPr marL="${(index - 1) * 457200}" algn="l" defTabSz="914400" rtl="0" eaLnBrk="1" latinLnBrk="0" hangingPunct="1"><a:defRPr sz="1200" kern="1200"><a:solidFill><a:schemeClr val="tx1"/></a:solidFill><a:latin typeface="+mn-lt"/><a:ea typeface="+mn-ea"/><a:cs typeface="+mn-cs"/></a:defRPr></a:lvl${index}pPr>`;
	return `${XML_DECLARATION}<p:notesMaster xmlns:a="${DRAWING_NS}" xmlns:r="${RELATIONSHIP_NS}" xmlns:p="${PRESENTATION_NS}"><p:cSld><p:bg><p:bgRef idx="1001"><a:schemeClr val="bg1"/></p:bgRef></p:bg><p:spTree><p:nvGrpSpPr><p:cNvPr id="1" name=""/><p:cNvGrpSpPr/><p:nvPr/></p:nvGrpSpPr><p:grpSpPr><a:xfrm><a:off x="0" y="0"/><a:ext cx="0" cy="0"/><a:chOff x="0" y="0"/><a:chExt cx="0" cy="0"/></a:xfrm></p:grpSpPr>` + buildPlaceholder(2, "Slide Image Placeholder 1", "<p:ph type=\"sldImg\" idx=\"2\"/>", { transform: box(imageTop, imageHeight) }) + buildPlaceholder(3, "Notes Placeholder 2", "<p:ph type=\"body\" sz=\"quarter\" idx=\"3\"/>", {
		transform: box(bodyTop, bodyHeight),
		body: "<p:txBody><a:bodyPr vert=\"horz\" lIns=\"91440\" tIns=\"45720\" rIns=\"91440\" bIns=\"45720\" rtlCol=\"0\"/><a:lstStyle/><a:p><a:endParaRPr lang=\"en-US\"/></a:p></p:txBody>"
	}) + `</p:spTree></p:cSld><p:clrMap bg1="lt1" tx1="dk1" bg2="lt2" tx2="dk2" accent1="accent1" accent2="accent2" accent3="accent3" accent4="accent4" accent5="accent5" accent6="accent6" hlink="hlink" folHlink="folHlink"/><p:notesStyle>${[
		1,
		2,
		3,
		4,
		5,
		6,
		7,
		8,
		9
	].map(level).join("")}</p:notesStyle></p:notesMaster>`;
}
/** A slide's notes page: its picture, then its notes, a paragraph a line. */
function buildNotesSlideXml(notes) {
	const paragraphs = notes.split(/\r?\n/).map((line) => line ? `<a:p><a:r><a:rPr lang="en-US" dirty="0"/><a:t>${escapeXml(line)}</a:t></a:r></a:p>` : "<a:p><a:endParaRPr lang=\"en-US\" dirty=\"0\"/></a:p>").join("");
	return `${XML_DECLARATION}<p:notes xmlns:a="${DRAWING_NS}" xmlns:r="${RELATIONSHIP_NS}" xmlns:p="${PRESENTATION_NS}"><p:cSld><p:spTree><p:nvGrpSpPr><p:cNvPr id="1" name=""/><p:cNvGrpSpPr/><p:nvPr/></p:nvGrpSpPr><p:grpSpPr><a:xfrm><a:off x="0" y="0"/><a:ext cx="0" cy="0"/><a:chOff x="0" y="0"/><a:chExt cx="0" cy="0"/></a:xfrm></p:grpSpPr>` + buildPlaceholder(2, "Slide Image Placeholder 1", "<p:ph type=\"sldImg\"/>") + buildPlaceholder(3, "Notes Placeholder 2", "<p:ph type=\"body\" idx=\"1\"/>", { body: `<p:txBody><a:bodyPr/><a:lstStyle/>${paragraphs}</p:txBody>` }) + "</p:spTree></p:cSld><p:clrMapOvr><a:masterClrMapping/></p:clrMapOvr></p:notes>";
}
/**
* Every slide names its own colours and typeface, so the theme exists only
* because the format requires the master to have one. It is the stock Office
* palette, with the three-entry style lists the schema insists on.
*/
function buildThemeXml() {
	const accents = [
		"4472C4",
		"ED7D31",
		"A5A5A5",
		"FFC000",
		"5B9BD5",
		"70AD47"
	].map((color, index) => `<a:accent${index + 1}><a:srgbClr val="${color}"/></a:accent${index + 1}>`).join("");
	const solidFill = "<a:solidFill><a:schemeClr val=\"phClr\"/></a:solidFill>";
	const outline = `<a:ln w="6350" cap="flat" cmpd="sng" algn="ctr">${solidFill}<a:prstDash val="solid"/></a:ln>`;
	return `${XML_DECLARATION}<a:theme xmlns:a="${DRAWING_NS}" name="Open Lyric"><a:themeElements><a:clrScheme name="Open Lyric"><a:dk1><a:sysClr val="windowText" lastClr="000000"/></a:dk1><a:lt1><a:sysClr val="window" lastClr="FFFFFF"/></a:lt1><a:dk2><a:srgbClr val="44546A"/></a:dk2><a:lt2><a:srgbClr val="E7E6E6"/></a:lt2>${accents}<a:hlink><a:srgbClr val="0563C1"/></a:hlink><a:folHlink><a:srgbClr val="954F72"/></a:folHlink></a:clrScheme><a:fontScheme name="Open Lyric"><a:majorFont><a:latin typeface="Calibri Light"/><a:ea typeface=""/><a:cs typeface=""/></a:majorFont><a:minorFont><a:latin typeface="Calibri"/><a:ea typeface=""/><a:cs typeface=""/></a:minorFont></a:fontScheme><a:fmtScheme name="Open Lyric"><a:fillStyleLst>${solidFill.repeat(3)}</a:fillStyleLst><a:lnStyleLst>${outline.repeat(3)}</a:lnStyleLst><a:effectStyleLst>${"<a:effectStyle><a:effectLst/></a:effectStyle>".repeat(3)}</a:effectStyleLst><a:bgFillStyleLst>${solidFill.repeat(3)}</a:bgFillStyleLst></a:fmtScheme></a:themeElements><a:objectDefaults/><a:extraClrSchemeLst/></a:theme>`;
}
/** A new, empty 16:9 deck. */
function createOpenLyricPresentation() {
	return new PptxPresentation();
}
//#endregion
//#region src/plugins/OpenLyric/preview/controller/pptx/text-slides.ts
/**
* The Open Lyric PowerPoint deck's text slides — title, lyric and message
* slides built from the song's presentation data
* (`createOpenLyricPresentationData`), with no page, preview or canvas behind
* them.
*
* The preview controller's PowerPoint export
* (`../export-powerpoint.ts`) delegates its text-slide methods here, and a host
* with no live preview — the `open-lyric-mcp` server rendering in Node — builds
* the whole deck through {@link buildOpenLyricTextPresentation}. The picture
* slides (one rasterized section per slide) stay in the controller: they need
* a rendered preview to photograph.
*/
/** `value` as a whole number of lines a slide holds: 1 to the maximum. */
function normalizeOpenLyricTextSlideLineCount(value) {
	const count = Math.round(Number(value));
	return Number.isFinite(count) && count >= 1 ? Math.min(count, 8) : 8;
}
/** The deck's palettes, keyed by the preview theme they follow. */
var OPEN_LYRIC_POWERPOINT_THEMES = Object.freeze({
	light: Object.freeze({
		accent: "0F766E",
		background: "F7F5EF",
		body: "1F2937",
		muted: "5B6C80",
		surface: "FFFFFF",
		surfaceBorder: "D8E3EA",
		title: "16324F"
	}),
	dark: Object.freeze({
		accent: "34D399",
		background: "0D1721",
		body: "E2E8F0",
		muted: "94A3B8",
		surface: "132434",
		surfaceBorder: "27435C",
		title: "F8FAFC"
	})
});
function getOpenLyricPowerPointTheme(themeName) {
	return { ...themeName === "light" ? OPEN_LYRIC_POWERPOINT_THEMES.light : OPEN_LYRIC_POWERPOINT_THEMES.dark };
}
/** Inner padding in points, in the `[left, right, bottom, top]` order the writer takes. */
function getOpenLyricPowerPointTextBoxMargin({ left = 0, right = left, top = 0, bottom = top } = {}) {
	return [
		left,
		right,
		bottom,
		top
	];
}
/**
* The notation's `{p: #N}` (strumming pattern) and `{c: …}` (arrangement cue)
* directives, with the space after one. They are directions to the band: the
* plain-text form keeps them so it reads back as notation, but a slide shows
* the song.
*/
var OPEN_LYRIC_SLIDE_DIRECTIVE_RE = /\{[pc]:[^{}\r\n]*\}[ \t]*/gu;
/**
* `line` as a slide shows it: tabs as spaces, no trailing space, and no
* directive — `null` when a directive was all the line held.
*/
function normalizeOpenLyricPowerPointLine(line) {
	const text = String(line ?? "");
	const withoutDirectives = text.replace(OPEN_LYRIC_SLIDE_DIRECTIVE_RE, "");
	const normalized = withoutDirectives.replace(/\t/g, "    ").replace(/\s+$/g, "");
	return !normalized.trim() && withoutDirectives !== text ? null : normalized;
}
function chunkOpenLyricPowerPointLineGroups(lineGroups, maxLinesPerSlide = 8) {
	const normalizedGroups = Array.isArray(lineGroups) ? lineGroups.flatMap((group) => {
		if (!Array.isArray(group) || !group.length) return [[""]];
		const lines = group.map(normalizeOpenLyricPowerPointLine).filter((line) => line !== null);
		return lines.length ? [lines] : [];
	}) : [];
	if (!normalizedGroups.length) return [[]];
	const chunks = [];
	let currentChunk = [];
	let currentLineCount = 0;
	normalizedGroups.forEach((group) => {
		const safeGroup = group.length ? group : [""];
		const groupLineCount = safeGroup.length;
		if (currentChunk.length && currentLineCount + groupLineCount > maxLinesPerSlide) {
			chunks.push(currentChunk);
			currentChunk = [];
			currentLineCount = 0;
		}
		if (!currentChunk.length && chunks.length && safeGroup.every((line) => !String(line ?? "").trim())) return;
		currentChunk.push(safeGroup);
		currentLineCount += groupLineCount;
	});
	if (currentChunk.length) chunks.push(currentChunk);
	return chunks.length ? chunks : [[]];
}
function flattenOpenLyricPowerPointChunk(chunk) {
	const lines = Array.isArray(chunk) ? chunk.flatMap((group) => {
		if (!Array.isArray(group) || !group.length) return [""];
		return group.map((line) => String(line ?? ""));
	}) : [];
	let startIndex = 0;
	let endIndex = lines.length;
	while (startIndex < endIndex && !String(lines[startIndex] ?? "").trim()) startIndex += 1;
	while (endIndex > startIndex && !String(lines[endIndex - 1] ?? "").trim()) endIndex -= 1;
	return lines.slice(startIndex, endIndex);
}
function buildOpenLyricPowerPointSlideTitle(sectionData, chunkIndex, totalChunks) {
	const baseTitle = sectionData?.repeatText ? `${sectionData.partName} (${sectionData.repeatText})` : sectionData?.partName || sectionData?.heading || "Song section";
	return totalChunks > 1 ? `${baseTitle} (${chunkIndex + 1}/${totalChunks})` : baseTitle;
}
/**
* The deck's opening slide, centred the way the preview heads the song: the
* title, the subtitle, then the Key/Time/Tempo line. With `backgroundImage`
* (the picture decks' slide fill) as its background it matches the slides
* that follow; the text stays text, editable in the deck.
*/
function addOpenLyricPowerPointTitleSlide(pptx, theme, presentationData, typography, { backgroundImage = "", notes = "" } = {}) {
	const slide = pptx.addSlide();
	slide.background = backgroundImage ? { data: backgroundImage } : { color: theme.background };
	slide.color = theme.body;
	slide.notes = notes;
	const centred = {
		x: .75,
		w: 11.83,
		margin: 0,
		align: "center",
		fontFace: typography.chromeFontFace
	};
	slide.addText(presentationData.title || "Untitled Song", {
		...centred,
		y: 1.9,
		h: 1.75,
		valign: "bottom",
		fit: "shrink",
		fontSize: 48,
		bold: true,
		color: theme.title
	});
	if (presentationData.secondaryText) slide.addText(presentationData.secondaryText, {
		...centred,
		y: 3.8,
		h: .55,
		fontSize: 22,
		color: theme.muted
	});
	if (presentationData.metaLine) slide.addText(presentationData.metaLine, {
		...centred,
		y: presentationData.secondaryText ? 4.45 : 3.8,
		h: .45,
		fontSize: 16,
		color: theme.body
	});
	return slide;
}
function addOpenLyricPowerPointMessageSlide(pptx, theme, presentationData, typography, { title, message, slideNumber, totalSlides }) {
	const slide = pptx.addSlide();
	slide.background = { color: theme.background };
	slide.color = theme.body;
	slide.addText(presentationData.title || "Open Lyric", {
		x: .75,
		y: .42,
		w: 10.8,
		h: .22,
		margin: 0,
		fontFace: typography.chromeFontFace,
		fontSize: 11,
		color: theme.muted
	});
	slide.addText(title, {
		x: .75,
		y: .78,
		w: 11.25,
		h: .45,
		margin: 0,
		fontFace: typography.chromeFontFace,
		fontSize: 24,
		bold: true,
		color: theme.title
	});
	slide.addText(message, {
		x: 1.05,
		y: 2,
		w: 11.1,
		h: 2.2,
		margin: getOpenLyricPowerPointTextBoxMargin({
			left: 18,
			right: 18,
			top: 12,
			bottom: 12
		}),
		fontFace: typography.chromeFontFace,
		fontSize: 16,
		color: theme.body,
		fill: { color: theme.surface },
		line: {
			color: theme.surfaceBorder,
			width: 1
		},
		align: "center",
		valign: "middle",
		fit: "shrink"
	});
	slide.addText(`${slideNumber}/${totalSlides}`, {
		x: 11.55,
		y: 6.84,
		w: .7,
		h: .2,
		margin: 0,
		fontFace: typography.chromeFontFace,
		fontSize: 9,
		color: theme.muted,
		align: "right"
	});
}
function addOpenLyricPowerPointLyricSlide(pptx, theme, presentationData, typography, { sectionData, chunkIndex, lines, slideNumber, totalSlides, totalChunks, textAlign = "left" }) {
	const slide = pptx.addSlide();
	slide.background = { color: theme.background };
	slide.color = theme.body;
	slide.addText(presentationData.title || "Open Lyric", {
		x: .75,
		y: .42,
		w: 10.8,
		h: .22,
		margin: 0,
		fontFace: typography.chromeFontFace,
		fontSize: 11,
		color: theme.muted
	});
	slide.addText(buildOpenLyricPowerPointSlideTitle(sectionData, chunkIndex, totalChunks), {
		x: .75,
		y: .78,
		w: 11.25,
		h: .45,
		margin: 0,
		fontFace: typography.chromeFontFace,
		fontSize: 24,
		bold: true,
		color: theme.title
	});
	slide.addText(lines.length ? lines.join("\n") : " ", {
		x: 1.05,
		y: 1.46,
		w: 11.1,
		h: 4.95,
		margin: getOpenLyricPowerPointTextBoxMargin({
			left: 24,
			right: 12,
			top: 12,
			bottom: 12
		}),
		fontFace: typography.lyricFontFace,
		fontSize: typography.lyricFontSize,
		color: theme.body,
		fill: { color: theme.surface },
		line: {
			color: theme.surfaceBorder,
			width: 1
		},
		align: textAlign,
		valign: "middle",
		fit: "shrink"
	});
	slide.addText(`${slideNumber}/${totalSlides}`, {
		x: 11.55,
		y: 6.84,
		w: .7,
		h: .2,
		margin: 0,
		fontFace: typography.chromeFontFace,
		fontSize: 9,
		color: theme.muted,
		align: "right"
	});
}
function buildOpenLyricPowerPointSlideDescriptors(presentationData, maxLinesPerSlide = 8) {
	return (presentationData?.sections || []).flatMap((sectionData) => {
		const chunks = chunkOpenLyricPowerPointLineGroups(sectionData.lineGroups, maxLinesPerSlide);
		return chunks.map((chunk, chunkIndex) => ({
			chunkIndex,
			lines: flattenOpenLyricPowerPointChunk(chunk),
			sectionData,
			totalChunks: chunks.length
		}));
	});
}
/**
* The whole deck as text slides: a title slide, then one lyric slide per
* chunk of each section in structure order — or a single message slide when
* the song has no sections to show. The same slides the preview's PowerPoint
* export falls back to when it cannot rasterize the preview.
*/
function buildOpenLyricTextPresentation(presentationData, { theme = getOpenLyricPowerPointTheme("dark"), typography = { ...OPEN_LYRIC_POWERPOINT_DEFAULT_TYPOGRAPHY }, linesPerSlide = 8, textAlign = "left", transition = null } = {}) {
	const pptx = createOpenLyricPresentation();
	pptx.transition = transition;
	const slideDescriptors = buildOpenLyricPowerPointSlideDescriptors(presentationData, normalizeOpenLyricTextSlideLineCount(linesPerSlide));
	const totalSlides = Math.max(2, slideDescriptors.length + 1);
	addOpenLyricPowerPointTitleSlide(pptx, theme, presentationData, typography);
	if (!slideDescriptors.length) addOpenLyricPowerPointMessageSlide(pptx, theme, presentationData, typography, {
		message: "No structured sections are available in the current Open Lyric preview.",
		slideNumber: 2,
		title: "No lyric slides available",
		totalSlides
	});
	else slideDescriptors.forEach((descriptor, index) => {
		addOpenLyricPowerPointLyricSlide(pptx, theme, presentationData, typography, {
			...descriptor,
			slideNumber: index + 2,
			totalSlides,
			textAlign
		});
	});
	return pptx;
}
//#endregion
//#region src/open-lyric-mcp/operations/rendering.ts
function toPreviewOptions(options = {}) {
	return {
		simplifyChords: Boolean(options.simplifyChords),
		hideBracketedKeys: Boolean(options.hideChords),
		hideLeadingBars: Boolean(options.hideLeadingBars),
		hideStrummingPatterns: Boolean(options.hideStrummingPatterns),
		hideAttachments: Boolean(options.hideAttachments),
		showComments: Boolean(options.showComments),
		hideNotes: Boolean(options.hideNotes),
		partNameFilter: String(options.section ?? "").trim()
	};
}
function prepareSongText(text, options = {}) {
	const source = String(text ?? "");
	return options.key ? transposeSong(source, { toKey: options.key }).text : source;
}
function requireSongConfig(text) {
	if (!createOpenLyricPresentationData(text, {})) throw new SongOperationError("The document has no ol:Config fence, so there is no song to render — check it with validate_song.");
}
/** The song as plain text: title, meta line, structure, then each section. */
function renderSongText(text, options = {}) {
	const source = prepareSongText(text, options);
	requireSongConfig(source);
	return renderOpenLyricPlainText(source, toPreviewOptions(options));
}
/**
* The preview's editing chrome: controls that act on the editor (add, remove,
* rename, reorder, open a menu) and mean nothing in a static copy. The editor
* itself keeps no such list — its print stylesheet hides only a few of these,
* and its own image/print exports remove just the lyric view's two toggles
* (`OPEN_LYRIC_EXPORT_CONTROL_SELECTOR`).
*/
var STATIC_VIEW_REMOVED_SELECTOR = [
	OPEN_LYRIC_EXPORT_CONTROL_SELECTOR,
	".ol-preview-add-section",
	".ol-preview-structure-repeat-controls",
	".ol-preview-config__add-button",
	".ol-preview-config__part-action",
	".ol-preview-config__text-edit",
	".ol-preview-config__locale-remove",
	".ol-preview-config__attachment-remove",
	".ol-preview-config__pattern-duplicate",
	".ol-preview-config__pattern-remove",
	".ol-preview-fence__rename",
	".ol-preview-fence__edit",
	".ol-preview-fence__delete",
	"input",
	"select",
	"textarea",
	"form",
	"template"
].join(", ");
/** Attributes that only describe what a button did when clicked. */
var BUTTON_ONLY_ATTRIBUTES = /* @__PURE__ */ new Set([
	"type",
	"title",
	"tabindex",
	"disabled",
	"aria-label",
	"aria-haspopup",
	"aria-expanded",
	"aria-pressed",
	"aria-controls",
	"data-preview-action"
]);
/**
* Turn a rendered view into a static one: drop the editing chrome above, and
* every other `<button>` — a chord, the tempo, a structure arrow, a pattern
* reference: content the preview made clickable — becomes a `<span>` with
* the same classes and text. A button with no text is an icon control, and
* goes. The attachments disclosure is opened, since nothing static can be.
*/
function toStaticViewHtml(html) {
	const container = document.createElement("div");
	container.innerHTML = html;
	container.querySelectorAll(STATIC_VIEW_REMOVED_SELECTOR).forEach((element) => element.remove());
	container.querySelectorAll("button").forEach((button) => {
		if (!button.textContent?.trim()) {
			button.remove();
			return;
		}
		const span = document.createElement("span");
		Array.from(button.attributes).forEach(({ name, value }) => {
			if (!BUTTON_ONLY_ATTRIBUTES.has(name)) span.setAttribute(name, value);
		});
		span.append(...Array.from(button.childNodes));
		button.replaceWith(span);
	});
	expandOpenLyricExtras(container);
	return container.innerHTML;
}
/** The lyric view's HTML fragment, static (style it with the preview stylesheet). */
function renderSongLyricHtml(text, options = {}) {
	const source = prepareSongText(text, options);
	requireSongConfig(source);
	return toStaticViewHtml(String(renderOpenLyricPreview(source, toPreviewOptions(options)) ?? ""));
}
/** The markdown view's HTML fragment, static: the whole document, fences as cards. */
function renderSongMarkdownHtml(text, options = {}) {
	const { partNameFilter: _partNameFilter, ...previewOptions } = toPreviewOptions(options);
	return toStaticViewHtml(String(renderMarkdownPreview(prepareSongText(text, options), previewOptions) ?? ""));
}
function readSongTitle(text) {
	return songObjectFromMarkdown(text).song.config.Title?.trim() || "";
}
function readDocumentLanguage(text) {
	const [firstLocale = ""] = songObjectFromMarkdown(text).song.config.Locales ?? [];
	return /^[A-Za-z]{2,3}(?:-[A-Za-z0-9]{2,8})*$/.test(firstLocale) ? firstLocale : "en";
}
/** The largest font file an export carries, as the editor's Word export. */
var SONG_EXPORT_FONT_MAX_BYTES = 4194304;
/** The formats that can carry a font file: the others only name theirs. */
var SONG_FONT_CARRYING_FORMATS = /* @__PURE__ */ new Set([
	"docx",
	"slideshow",
	"html"
]);
/** Whether `bytes` starts as a TrueType font does (`0x00010000` or `true`). */
function isTrueTypeFontFile(bytes) {
	const version = bytes.length >= 4 ? (bytes[0] << 24 >>> 0) + (bytes[1] << 16) + (bytes[2] << 8) + bytes[3] : 0;
	return version === 65536 || version === 1953658213;
}
/**
* `fontData`, once it is a font `format` can carry under `fontFace`: a
* TrueType file of at most {@link SONG_EXPORT_FONT_MAX_BYTES} whose maker
* lets it travel in a document (`OS/2` `fsType`). `null` without one; a
* {@link SongOperationError} saying what is wrong otherwise.
*/
function requireEmbeddableSongFont(fontData, fontFace, format) {
	if (fontData === void 0) return null;
	if (!SONG_FONT_CARRYING_FORMATS.has(format)) throw new SongOperationError(`A font file is carried by docx, slideshow and html; a ${format} export only names its font (fontFace).`);
	if (!String(fontFace ?? "").trim()) throw new SongOperationError("A font file needs fontFace: the family name the text is set in, as the font calls itself (e.g. Battambang).");
	if (!ArrayBuffer.isView(fontData)) throw new SongOperationError("The font file must be given as bytes.");
	const bytes = new Uint8Array(fontData.buffer, fontData.byteOffset, fontData.byteLength);
	if (!bytes.length) throw new SongOperationError("The font file is empty.");
	if (bytes.length > 4194304) throw new SongOperationError(`The font file is ${bytes.length} bytes; the limit is ${SONG_EXPORT_FONT_MAX_BYTES}.`);
	if (!isTrueTypeFontFile(bytes)) throw new SongOperationError("The font file must be a TrueType font (.ttf). OpenType-CFF (.otf), WOFF and WOFF2 files are not carried.");
	if (!isEmbeddableTrueTypeFont(bytes)) throw new SongOperationError("The font’s maker does not allow embedding it in documents (its OS/2 fsType), so it is not carried. Leave out the font file: fontFace still names it.");
	return bytes;
}
/** The `@font-face` rule that declares `fontData` as `face`, the file written in. */
function renderEmbeddedFontFaceCss(face, fontData) {
	return fontData ? `@font-face { font-family: ${toCssFontFamilyString(face.trim())}; src: url("data:font/ttf;base64,${Buffer.from(fontData).toString("base64")}") format("truetype"); font-display: swap; }\n` : "";
}
/** The page's own font stack, after the one `fontFace` names. */
var HTML_DOCUMENT_FONT_STACK = "system-ui, -apple-system, 'Segoe UI', Roboto, 'Noto Sans', 'Noto Sans Khmer', sans-serif";
/**
* `face` as a CSS string: quoted, with what could end the string or the
* `<style>` element around it escaped.
*/
function toCssFontFamilyString(face) {
	return `"${face.replace(/["\\<>\r\n\f]/g, (character) => `\\${character.codePointAt(0).toString(16).toUpperCase()} `)}"`;
}
function renderHtmlDocumentFontCss(fontFace) {
	const face = String(fontFace ?? "").trim();
	return face ? `\nbody { font-family: ${toCssFontFamilyString(face)}, ${HTML_DOCUMENT_FONT_STACK}; }` : "";
}
/** A standalone HTML page — the chosen view with the preview styles inlined. */
function renderSongHtmlDocument(text, { view = "lyric", theme = "light", fontFace, fontData, ...options } = {}) {
	const fontFaceCss = renderEmbeddedFontFaceCss(String(fontFace ?? ""), requireEmbeddableSongFont(fontData, fontFace, "html"));
	const body = view === "markdown" ? renderSongMarkdownHtml(text, options) : renderSongLyricHtml(text, options);
	const title = readSongTitle(text) || "Open Lyric song";
	const themeName = theme === "dark" ? "dark" : "light";
	return [
		"<!doctype html>",
		`<html lang="${escapeHtml$1(readDocumentLanguage(text))}" data-theme="${themeName}" data-ol-theme="${themeName}">`,
		"<head>",
		"<meta charset=\"utf-8\">",
		"<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">",
		"<meta name=\"generator\" content=\"open-lyric-mcp\">",
		`<title>${escapeHtml$1(title)}</title>`,
		`<style>\n${fontFaceCss}${document_theme_default}${renderHtmlDocumentFontCss(fontFace)}\n${getInjectablePreviewStyleCss()}\n</style>`,
		"</head>",
		"<body>",
		`<main class="ol-preview-root open-lyric-render-surface ol-mcp-document" data-ol-view="${view}">`,
		body,
		"</main>",
		"</body>",
		"</html>",
		""
	].join("\n");
}
function renderSong(text, format, options = {}) {
	switch (format) {
		case "text": return renderSongText(text, options);
		case "lyric-html": return renderSongLyricHtml(text, options);
		case "markdown-html": return renderSongMarkdownHtml(text, options);
		case "html-document": return renderSongHtmlDocument(text, options);
		default: throw new SongOperationError(`Unknown render format "${String(format)}".`);
	}
}
var SONG_EXPORT_FORMATS = {
	md: {
		extension: ".ol.md",
		mimeType: "text/markdown",
		binary: false
	},
	json: {
		extension: ".json",
		mimeType: "application/json",
		binary: false
	},
	txt: {
		extension: ".txt",
		mimeType: "text/plain",
		binary: false
	},
	html: {
		extension: ".html",
		mimeType: "text/html",
		binary: false
	},
	docx: {
		extension: ".docx",
		mimeType: "application/vnd.openxmlformats-officedocument.wordprocessingml.document",
		binary: true
	},
	pptx: {
		extension: ".pptx",
		mimeType: "application/vnd.openxmlformats-officedocument.presentationml.presentation",
		binary: true
	},
	slideshow: {
		extension: ".html",
		mimeType: HTML_MIME_TYPE,
		binary: false
	}
};
/** The lyrics' size in points: the default and the range. */
var SONG_DECK_FONT_SIZE = Object.freeze({
	default: OPEN_LYRIC_POWERPOINT_DEFAULT_TYPOGRAPHY.lyricFontSize,
	min: 12,
	max: 96
});
/** Every transition a deck can come on with: `none`, or one of the catalogue's. */
var SONG_DECK_TRANSITIONS = Object.freeze(["none", ...OPEN_LYRIC_POWERPOINT_TRANSITION_SPECS.map((spec) => spec.id)]);
/**
* A file-name stem from the song title: path-unsafe characters removed, and
* the invisible ones — a Khmer title's zero-width word breaks (U+200B), ZWNJ,
* ZWJ, word joiner, BOM — dropped, so the name is what it looks like.
*/
function createSongFileStem(text) {
	return readSongTitle(text).replace(/[\u200b-\u200d\u2060\ufeff]+/gu, "").replace(/[\\/:*?"<>|\u0000-\u001f]+/g, " ").replace(/\s+/g, " ").trim().slice(0, 120) || "open-lyric-song";
}
async function exportDocx(text, { fontFace, fontData, ...options }) {
	const docxModule = await import("docx");
	const root = document.createElement("div");
	root.innerHTML = renderSongMarkdownHtml(text, options);
	const face = String(fontFace ?? "").trim();
	const documentFile = createMarkdownPreviewDocxDocument(docxModule, root, {
		title: readSongTitle(text) || "Open Lyric song",
		...face ? { bodyFontFamily: face } : {},
		fonts: face && fontData ? [{
			name: face,
			data: fontData
		}] : []
	});
	return new Uint8Array(await docxModule.Packer.toBuffer(documentFile, void 0, getMarkdownPreviewDocxPackOverrides(documentFile)));
}
function requireWholeNumber(value, name, min, max) {
	if (value === void 0) return;
	if (!Number.isInteger(value) || value < min || value > max) throw new SongOperationError(`${name} must be a whole number from ${min} to ${max}.`);
	return value;
}
function toDeckTypography({ fontFace, fontSize }, isChordShown) {
	const face = String(fontFace ?? "").trim();
	const defaults = OPEN_LYRIC_POWERPOINT_DEFAULT_TYPOGRAPHY;
	return {
		chromeFontFace: face || defaults.chromeFontFace,
		lyricFontFace: face || (isChordShown ? defaults.lyricFontFace : defaults.chromeFontFace),
		lyricFontSize: requireWholeNumber(fontSize, "fontSize", SONG_DECK_FONT_SIZE.min, SONG_DECK_FONT_SIZE.max) ?? SONG_DECK_FONT_SIZE.default
	};
}
function toDeckTransition({ transition, transitionSpeed }) {
	const id = String(transition ?? "").trim() || "none";
	if (id === "none") return null;
	if (!getOpenLyricPowerPointTransitionSpec(id)) throw new SongOperationError(`Unknown transition "${id}". Use one of: ${SONG_DECK_TRANSITIONS.join(", ")}.`);
	if (transitionSpeed !== void 0 && ![
		"slow",
		"medium",
		"fast"
	].includes(transitionSpeed)) throw new SongOperationError("transitionSpeed must be slow, medium or fast.");
	return {
		type: id,
		speed: !transitionSpeed || transitionSpeed === "medium" ? "med" : transitionSpeed,
		direction: resolveOpenLyricPowerPointTransitionDirection(id, "")
	};
}
/**
* The PowerPoint deck of text slides, for both the `.pptx` and the slide
* show page: the song in performance order (`section` does not apply),
* lyrics only unless `hideChords` is `false`.
*/
function buildSongPresentation(text, theme, { hideChords = true, ...viewOptions }) {
	const options = {
		...viewOptions,
		hideChords
	};
	if (options.textAlign !== void 0 && ![
		"left",
		"center",
		"right"
	].includes(options.textAlign)) throw new SongOperationError("textAlign must be left, center or right.");
	const linesPerSlide = requireWholeNumber(options.linesPerSlide, "linesPerSlide", 1, 8);
	const typography = toDeckTypography(options, !hideChords);
	const transition = toDeckTransition(options);
	const source = prepareSongText(text, options);
	const { partNameFilter: _partNameFilter, ...previewOptions } = toPreviewOptions(options);
	const presentationData = createOpenLyricPresentationData(source, previewOptions);
	if (!presentationData) throw new SongOperationError("The document has no ol:Config fence, so there is no song to export.");
	if (hideChords) presentationData.sections = presentationData.sections.map((section) => ({
		...section,
		lineGroups: section.lineGroups.flatMap((group) => {
			const lines = group.filter((line) => !isProgressionLineText(line));
			return lines.length || !group.length ? [lines] : [];
		})
	}));
	return {
		presentation: buildOpenLyricTextPresentation(presentationData, {
			theme: getOpenLyricPowerPointTheme(theme === "light" ? "light" : "dark"),
			typography,
			linesPerSlide,
			textAlign: options.textAlign,
			transition
		}),
		title: presentationData.title
	};
}
async function exportPptx(text, theme, options) {
	const { presentation } = buildSongPresentation(text, theme, options);
	const blob = await presentation.write({ compression: true });
	return new Uint8Array(await blob.arrayBuffer());
}
/**
* The deck {@link exportPptx} writes, as the self-contained HTML slide show
* page (viewer, presenter view, transitions) — its words in English, its
* text in the faces the viewer's computer has.
*/
function exportSlideshow(text, theme, options, fontData = null) {
	const { presentation, title } = buildSongPresentation(text, theme, options);
	const fontCss = renderEmbeddedFontFaceCss(String(options.fontFace ?? ""), fontData);
	return buildOpenLyricPresentationHtml(presentation.toData(), {
		title,
		...fontCss ? { fontCss } : {}
	});
}
async function exportSong(text, { format, theme, view, fontData: givenFontData, ...options }) {
	const spec = SONG_EXPORT_FORMATS[format];
	if (!spec) throw new SongOperationError(`Unknown export format "${String(format)}". Use one of: ${Object.keys(SONG_EXPORT_FORMATS).join(", ")}.`);
	const fontData = requireEmbeddableSongFont(givenFontData, options.fontFace, format);
	let data;
	switch (format) {
		case "md":
			data = prepareSongText(text, options);
			break;
		case "json":
			data = `${JSON.stringify(songObjectFromMarkdown(prepareSongText(text, options)).song, null, 2)}\n`;
			break;
		case "txt":
			data = renderSongText(text, options);
			break;
		case "html":
			data = renderSongHtmlDocument(text, {
				...options,
				theme,
				view,
				...fontData ? { fontData } : {}
			});
			break;
		case "docx":
			data = await exportDocx(prepareSongText(text, options), {
				...options,
				key: void 0,
				fontData
			});
			break;
		case "pptx":
			data = await exportPptx(text, theme ?? "dark", options);
			break;
		case "slideshow": data = exportSlideshow(text, theme ?? "dark", options, fontData);
	}
	return {
		format,
		mimeType: spec.mimeType,
		fileName: `${createSongFileStem(text)}${spec.extension}`,
		data
	};
}
//#endregion
//#region src/open-lyric-mcp/tools/rendering.ts
var EXPORT_FORMATS = Object.keys(SONG_EXPORT_FORMATS);
/**
* The bytes of `fontFile`, a file inside the allowed roots, refused before it
* is read when it is larger than an export carries. `exportSong` then checks
* it is a TrueType font its maker lets travel.
*/
async function readFontFile(files, fontFile) {
	const resolved = await files.resolveForRead(fontFile);
	const stats = await stat(resolved);
	if (!stats.isFile()) throw new Error(`${resolved} is not a file.`);
	if (stats.size > 4194304) throw new Error(`${resolved} is ${stats.size} bytes; a font file may be at most ${SONG_EXPORT_FONT_MAX_BYTES}.`);
	return new Uint8Array(await readFile(resolved));
}
/** The deck layout `export_song` takes for pptx and slideshow. */
var deckOptionsShape = {
	linesPerSlide: z.number().int().min(1).max(8).optional().describe(`pptx and slideshow: the most lyric lines a slide holds. Default 8; 2 is the usual worship-screen look.`),
	fontFace: z.string().trim().min(1).max(100).optional().describe("The font, named in the file — pick one with glyphs for the song’s script, e.g. Battambang for Khmer; with fontFile, docx, slideshow and html carry it too. pptx and slideshow: titles and lyrics alike, default Arial (Courier New for the lyrics when chords are shown). docx: every run, default Calibri. html: the page, ahead of the system font stack it falls back to."),
	fontSize: z.number().int().min(SONG_DECK_FONT_SIZE.min).max(SONG_DECK_FONT_SIZE.max).optional().describe(`pptx and slideshow: the lyrics' size in points. Default ${SONG_DECK_FONT_SIZE.default}.`),
	textAlign: z.enum([
		"left",
		"center",
		"right"
	]).optional().describe("pptx and slideshow: how the lyrics sit across the slide. Default left; keep left when chords are shown."),
	transition: z.enum(SONG_DECK_TRANSITIONS).optional().describe("pptx and slideshow: how every slide comes on, e.g. fade, push or morph. Default none."),
	transitionSpeed: z.enum([
		"slow",
		"medium",
		"fast"
	]).optional().describe("pptx and slideshow, with a transition. Default medium.")
};
function registerRenderingTools({ server, files }) {
	server.registerTool("render_song", {
		title: "Render a song",
		description: "Render through the editor's renderers. text: the plain-text song (title, meta, structure, sections in performance order). lyric-html: the lyric view fragment. markdown-html: the whole document with fences as cards. html-document: a standalone page with the stylesheet inlined (large — to save it, use export_song with outputPath).",
		inputSchema: {
			...songSourceShape,
			format: z.enum([
				"text",
				"lyric-html",
				"markdown-html",
				"html-document"
			]),
			...viewOptionsShape,
			view: z.enum(["lyric", "markdown"]).optional().describe("html-document only: which view. Default lyric."),
			theme: z.enum(["light", "dark"]).optional().describe("html-document only.")
		},
		outputSchema: {
			format: z.string(),
			output: z.string()
		},
		annotations: {
			readOnlyHint: true,
			openWorldHint: false
		}
	}, ({ text, path, format, ...options }) => runTool(async () => {
		const output = renderSong((await readSongSource(files, {
			text,
			path
		})).text, format, options);
		return {
			content: [{
				type: "text",
				text: output
			}],
			structuredContent: {
				format,
				output
			}
		};
	}));
	server.registerTool("export_song", {
		title: "Export a song",
		description: "Export to a file format: docx (Word, from the markdown view), pptx (PowerPoint text slides: a title slide, then the sections in performance order, lyrics only unless hideChords is false; laid out with linesPerSlide, fontFace, fontSize, textAlign and transition), slideshow (that same deck as one self-contained .html slide show page — viewer, presenter view, transitions; large, so prefer outputPath), html (standalone page), txt, json (the song object) or md (the notation, transposed when key is given). With outputPath the file is written inside the allowed roots; without it the file comes back as an embedded resource.",
		inputSchema: {
			...songSourceShape,
			format: z.enum(EXPORT_FORMATS),
			outputPath: z.string().optional().describe("Write here (inside the allowed roots); the extension must match the format."),
			overwrite: z.boolean().optional().describe("Replace an existing file. Default false."),
			...viewOptionsShape,
			view: z.enum(["lyric", "markdown"]).optional().describe("html only. Default lyric."),
			theme: z.enum(["light", "dark"]).optional().describe("html (default light), pptx and slideshow (default dark)."),
			...deckOptionsShape,
			fontFile: z.string().optional().describe(`docx, slideshow and html: a TrueType font file (.ttf, up to ${SONG_EXPORT_FONT_MAX_BYTES / 1024 / 1024} MB) inside the allowed roots, carried in the export under fontFace (required with it) so the text reads in that face on a computer without it — Word embeds it, the pages declare it. Refused when its maker does not allow embedding. Other formats refuse it.`)
		},
		outputSchema: {
			format: z.string(),
			fileName: z.string(),
			mimeType: z.string(),
			bytes: z.number(),
			path: z.string().optional(),
			written: z.boolean()
		},
		annotations: {
			readOnlyHint: false,
			destructiveHint: false,
			openWorldHint: false
		}
	}, ({ text, path, format, outputPath, overwrite, fontFile, ...options }) => runTool(async () => {
		const source = await readSongSource(files, {
			text,
			path
		});
		const fontData = fontFile ? await readFontFile(files, fontFile) : void 0;
		const exported = await exportSong(source.text, {
			format,
			...options,
			...fontData ? { fontData } : {}
		});
		const data = typeof exported.data === "string" ? Buffer.from(exported.data, "utf8") : Buffer.from(exported.data);
		const spec = SONG_EXPORT_FORMATS[format];
		const metadata = {
			format,
			fileName: exported.fileName,
			mimeType: exported.mimeType,
			bytes: data.byteLength
		};
		if (outputPath) {
			const target = await files.resolveForWrite(outputPath, [spec.extension === ".ol.md" ? ".md" : spec.extension]);
			if (!overwrite) {
				if (await files.resolveForRead(target).then(() => true, () => false)) throw new Error(`${target} already exists — pass overwrite: true to replace it.`);
			}
			const written = await files.writeFile(target, exported.data, []);
			return {
				content: [{
					type: "text",
					text: `Wrote ${written.path} (${format}, ${written.bytes} bytes).`
				}],
				structuredContent: {
					...metadata,
					path: written.path,
					written: true
				}
			};
		}
		const uri = `open-lyric://exports/${encodeURIComponent(exported.fileName)}`;
		return {
			content: [{
				type: "text",
				text: `Exported ${exported.fileName} (${format}, ${data.byteLength} bytes).`
			}, {
				type: "resource",
				resource: spec.binary ? {
					uri,
					mimeType: exported.mimeType,
					blob: data.toString("base64")
				} : {
					uri,
					mimeType: exported.mimeType,
					text: exported.data
				}
			}],
			structuredContent: {
				...metadata,
				written: false
			}
		};
	}));
}
//#endregion
//#region src/open-lyric-mcp/version.ts
/** The `open-lyric-mcp` package version, reported as the server version. */
var OPEN_LYRIC_MCP_VERSION = "0.1.18";
//#endregion
//#region src/open-lyric-mcp/server.ts
var OPEN_LYRIC_MCP_INSTRUCTIONS = `Open Lyric songs are Markdown documents with \`\`\`ol:<Section> fences: one ol:Config fence (Title and Structure required; Key, Tempo, Time, Locales …) and one fence per section (Verse 1, Chorus, Bridge, Intro …). Chords are [G] annotations placed just before the syllable they land on; Intro/Outro/Instrumental lines may be bar progressions (| G | D/F# |). Structure is the compact performance order, e.g. IV1CV2CBCx2O.

- Before writing notation by hand, read open-lyric://docs/notation (or get_notation_reference).
- Prefer the structural tools (create_song, add_section, rename_section, set_config_field, transpose_song …): they keep Structure in step and return the validation.
- After any change, make sure validate_song reports no errors; diagnostics carry 1-based lines and columns, and apply_fixes applies every one that carries a fix.
- Song files (*.ol.md) are read and written only inside the allowed roots. Tools given a path edit that file in place — pass dryRun to preview.`;
/**
* An MCP server exposing the Open Lyric notation: validation, analysis, music
* theory, structural editing, rendering and export, song files, reference
* resources and prompts. Connect it to a transport (`runStdioServer`,
* `runHttpServer`, or the SDK's own).
*/
function createOpenLyricMcpServer(options = {}) {
	const readOnly = Boolean(options.readOnly);
	const server = new McpServer({
		name: "open-lyric",
		title: "Open Lyric",
		version: OPEN_LYRIC_MCP_VERSION
	}, { instructions: OPEN_LYRIC_MCP_INSTRUCTIONS });
	const files = new FileAccess({
		configuredRoots: options.roots ?? [],
		readOnly,
		cwd: options.cwd,
		listClientRoots: options.listClientRoots ?? createClientRootsLister(server)
	});
	const context = {
		server,
		files
	};
	registerAnalysisTools(context);
	registerMusicTools(context);
	registerEditingTools(context);
	registerRenderingTools(context);
	registerFileTools(context, { readOnly });
	registerReferenceTools(context);
	registerOpenLyricResources(server);
	registerOpenLyricPrompts(server, files);
	return server;
}
//#endregion
//#region src/mcp-common/transports.ts
/**
* The two ways the Open Lyric MCP servers are reached: stdio (one client, the
* process that started the server — what `npx`-launched servers use) and
* Streamable HTTP (any number of clients on a port).
*
* The HTTP server is stateless: every POST gets a fresh `McpServer` and
* transport, so no session state is kept between requests. It listens on
* loopback by default and turns on the SDK's DNS-rebinding protection for
* loopback hosts.
*/
async function runStdioServer(server) {
	const transport = new StdioServerTransport();
	await server.connect(transport);
}
var LOOPBACK_HOSTS = /* @__PURE__ */ new Set([
	"127.0.0.1",
	"localhost",
	"::1"
]);
function sendJsonRpcError(response, status, message, headers = {}) {
	if (response.headersSent) {
		response.end();
		return;
	}
	response.writeHead(status, {
		"Content-Type": "application/json",
		...headers
	});
	response.end(JSON.stringify({
		jsonrpc: "2.0",
		error: {
			code: -32e3,
			message
		},
		id: null
	}));
}
async function runHttpServer(createServer$1, { port = 3333, host = "127.0.0.1", path = "/mcp", log = () => {} } = {}) {
	const httpServer = createServer(async (request, response) => {
		if (new URL(request.url ?? "/", "http://localhost").pathname !== path) {
			sendJsonRpcError(response, 404, `Not found. The MCP endpoint is ${path}.`);
			return;
		}
		if (request.method !== "POST") {
			sendJsonRpcError(response, 405, "Method not allowed.", { Allow: "POST" });
			return;
		}
		const server = createServer$1();
		const address = httpServer.address();
		const boundPort = address && typeof address === "object" ? address.port : port;
		const transport = new StreamableHTTPServerTransport({
			sessionIdGenerator: void 0,
			...LOOPBACK_HOSTS.has(host) ? {
				enableDnsRebindingProtection: true,
				allowedHosts: [
					`127.0.0.1:${boundPort}`,
					`localhost:${boundPort}`,
					`[::1]:${boundPort}`
				]
			} : {}
		});
		response.on("close", () => {
			transport.close();
			server.close();
		});
		try {
			await server.connect(transport);
			await transport.handleRequest(request, response);
		} catch (error) {
			log(`HTTP request failed: ${error instanceof Error ? error.message : String(error)}`);
			sendJsonRpcError(response, 500, "Internal server error.");
		}
	});
	await new Promise((resolve, reject) => {
		httpServer.once("error", reject);
		httpServer.listen(port, host, () => {
			httpServer.off("error", reject);
			resolve();
		});
	});
	const address = httpServer.address();
	const boundPort = address && typeof address === "object" ? address.port : port;
	return {
		url: `http://${host.includes(":") ? `[${host}]` : host}:${boundPort}${path}`,
		close: () => new Promise((resolve) => {
			httpServer.close(() => resolve());
			httpServer.closeAllConnections?.();
		})
	};
}
//#endregion
export { listNotationSections as A, importPlainText as B, getNotationGrammar as C, listExamples as D, listConfigFields as E, createSong as F, SongOperationError as G, setConfigField as H, deleteSection as I, listSongChords as J, describeStructure as K, deriveStructure as L, KHMER_FORMAT_HINT as M, addSection as N, listFenceTypes as O, applyFixes as P, formatSong as R, getNotationDocument as S, getSongJsonSchema as T, setSectionLines as U, renameSection as V, songFromObject as W, summarizeValidation as X, listSongSections as Y, validateSong as Z, describeChord as _, OPEN_LYRIC_MCP_VERSION as a, transposeSong as b, SONG_EXPORT_FONT_MAX_BYTES as c, exportSong as d, renderSong as f, renderSongText as g, renderSongMarkdownHtml as h, createOpenLyricMcpServer as i, listStructureCodes as j, listKeys as k, SONG_EXPORT_FORMATS as l, renderSongLyricHtml as m, runStdioServer as n, SONG_DECK_FONT_SIZE as o, renderSongHtmlDocument as p, getSongInfo as q, OPEN_LYRIC_MCP_INSTRUCTIONS as r, SONG_DECK_TRANSITIONS as s, runHttpServer as t, createSongFileStem as u, getKeyChords as v, getNotationSection as w, getExample as x, transposeChord as y, getSectionLines as z };

//# sourceMappingURL=transports-CcOWNL0M.js.map