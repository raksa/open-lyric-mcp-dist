import { A as listNotationSections, B as importPlainText, C as getNotationGrammar, D as listExamples, E as listConfigFields, F as createSong, G as SongOperationError, H as setConfigField, I as deleteSection, J as listSongChords, K as describeStructure, L as deriveStructure, M as KHMER_FORMAT_HINT, N as addSection, O as listFenceTypes, P as applyFixes, R as formatSong, S as getNotationDocument, T as getSongJsonSchema, U as setSectionLines, V as renameSection, W as songFromObject, X as summarizeValidation, Y as listSongSections, Z as validateSong, _ as describeChord, a as OPEN_LYRIC_MCP_VERSION, b as transposeSong, c as SONG_EXPORT_FONT_MAX_BYTES, d as exportSong, f as renderSong, g as renderSongText, h as renderSongMarkdownHtml, i as createOpenLyricMcpServer, j as listStructureCodes, k as listKeys, l as SONG_EXPORT_FORMATS, m as renderSongLyricHtml, n as runStdioServer, o as SONG_DECK_FONT_SIZE, p as renderSongHtmlDocument, q as getSongInfo, r as OPEN_LYRIC_MCP_INSTRUCTIONS, s as SONG_DECK_TRANSITIONS, t as runHttpServer, u as createSongFileStem, v as getKeyChords, w as getNotationSection, x as getExample, y as transposeChord, z as getSectionLines } from "./chunks/transports-DqYB-keg.js";
//#region \0rolldown/runtime.js
var __defProp = Object.defineProperty;
var __exportAll = (all, no_symbols) => {
	let target = {};
	for (var name in all) __defProp(target, name, {
		get: all[name],
		enumerable: true
	});
	if (!no_symbols) __defProp(target, Symbol.toStringTag, { value: "Module" });
	return target;
};
//#endregion
//#region src/open-lyric-mcp/operations/index.ts
var operations_exports = /* @__PURE__ */ __exportAll({
	KHMER_FORMAT_HINT: () => KHMER_FORMAT_HINT,
	SONG_DECK_FONT_SIZE: () => SONG_DECK_FONT_SIZE,
	SONG_DECK_MAX_LINES_PER_SLIDE: () => 8,
	SONG_DECK_TRANSITIONS: () => SONG_DECK_TRANSITIONS,
	SONG_EXPORT_FONT_MAX_BYTES: () => SONG_EXPORT_FONT_MAX_BYTES,
	SONG_EXPORT_FORMATS: () => SONG_EXPORT_FORMATS,
	SongOperationError: () => SongOperationError,
	addSection: () => addSection,
	applyFixes: () => applyFixes,
	createSong: () => createSong,
	createSongFileStem: () => createSongFileStem,
	deleteSection: () => deleteSection,
	deriveStructure: () => deriveStructure,
	describeChord: () => describeChord,
	describeStructure: () => describeStructure,
	exportSong: () => exportSong,
	formatSong: () => formatSong,
	getExample: () => getExample,
	getKeyChords: () => getKeyChords,
	getNotationDocument: () => getNotationDocument,
	getNotationGrammar: () => getNotationGrammar,
	getNotationSection: () => getNotationSection,
	getSectionLines: () => getSectionLines,
	getSongInfo: () => getSongInfo,
	getSongJsonSchema: () => getSongJsonSchema,
	importPlainText: () => importPlainText,
	listConfigFields: () => listConfigFields,
	listExamples: () => listExamples,
	listFenceTypes: () => listFenceTypes,
	listKeys: () => listKeys,
	listNotationSections: () => listNotationSections,
	listSongChords: () => listSongChords,
	listSongSections: () => listSongSections,
	listStructureCodes: () => listStructureCodes,
	renameSection: () => renameSection,
	renderSong: () => renderSong,
	renderSongHtmlDocument: () => renderSongHtmlDocument,
	renderSongLyricHtml: () => renderSongLyricHtml,
	renderSongMarkdownHtml: () => renderSongMarkdownHtml,
	renderSongText: () => renderSongText,
	setConfigField: () => setConfigField,
	setSectionLines: () => setSectionLines,
	songFromObject: () => songFromObject,
	summarizeValidation: () => summarizeValidation,
	transposeChord: () => transposeChord,
	transposeSong: () => transposeSong,
	validateSong: () => validateSong
});
//#endregion
export { OPEN_LYRIC_MCP_INSTRUCTIONS, createOpenLyricMcpServer, operations_exports as operations, runHttpServer, runStdioServer, OPEN_LYRIC_MCP_VERSION as version };

//# sourceMappingURL=index.js.map