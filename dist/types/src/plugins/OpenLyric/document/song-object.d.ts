/**
 * An Open Lyric song as a structured object — the shape of the JSON Schema in
 * the notation's knowledge doc (`schema.md` §8.2): the `ol:Config` fence as
 * typed fields plus every other fence, in written order, as
 * `{ header, index?, lines }`.
 *
 * {@link songObjectFromMarkdown} reads one out of a document and
 * {@link songObjectToMarkdown} writes one back as notation. The object carries
 * only what the schema can: Markdown outside the `ol:` fences comes back
 * separately as `preamble`, and what a song object has no slot for — a comment
 * inside a Config field other than a strumming-pattern label, an unsupported
 * Config field, a second Config fence — is reported in `warnings` rather than
 * silently dropped. Cross-references (Structure tokens, `{p: #N}`, duplicate
 * part names) are not checked here; run the serialized text through the
 * validator for those (§8.3).
 */
interface OpenLyricSongStrummingPattern {
    label?: string;
    pattern: string;
}
interface OpenLyricSongConfig {
    Title: string;
    Structure: string;
    Subtitle?: string;
    Description?: string[];
    Artist?: string;
    Copyright?: string;
    Locales?: string[];
    Key?: string;
    Tempo?: string;
    Time?: string;
    Theme?: string;
    Genre?: string;
    Style?: string;
    Keywords?: string[];
    Year?: string;
    Melody?: string;
    Attachments?: string[];
    'Strumming Patterns'?: OpenLyricSongStrummingPattern[];
}
interface OpenLyricSongSection {
    header: string;
    index?: number;
    lines: string[];
}
interface OpenLyricSong {
    config: OpenLyricSongConfig;
    sections: OpenLyricSongSection[];
}
interface OpenLyricSongReadResult {
    song: OpenLyricSong;
    /** The Markdown outside every `ol:` fence, blank edges trimmed. */
    preamble: string;
    /** Whatever the document holds that the song object cannot carry. */
    warnings: string[];
}
interface OpenLyricSongWriteOptions {
    /** Markdown written above the fences — typically a `# Title` and a note. */
    preamble?: string;
    /** Indent for continuation lines of multiline Config fields. Default tab. */
    indent?: string;
}
/**
 * Read a song object out of an Open Lyric document. Fences with an
 * unrecognized header are not sections and stay out of the object (and out of
 * the preamble); the validator reports them.
 */
declare function songObjectFromMarkdown(markdown: unknown): OpenLyricSongReadResult;
/**
 * The notation lines one Config field is written as — `- Name: value`, plus
 * indented continuation lines for the multiline fields (`Description`,
 * `Attachments`, `Strumming Patterns`, whose labels are `//` lines above their
 * pattern). An empty value writes nothing. `name` must be canonical (aliases
 * already resolved).
 */
declare function formatConfigFieldLines(name: string, value: unknown, indent?: string): string[];
/**
 * Write a song object as an Open Lyric document: the optional preamble, the
 * `ol:Config` fence with its fields in canonical order, then every section in
 * the object's order. Fields outside the schema are ignored. The result is
 * not validated here.
 */
declare function songObjectToMarkdown(song: OpenLyricSong, { preamble, indent }?: OpenLyricSongWriteOptions): string;
export { formatConfigFieldLines, songObjectFromMarkdown, songObjectToMarkdown };
export type { OpenLyricSong, OpenLyricSongConfig, OpenLyricSongReadResult, OpenLyricSongSection, OpenLyricSongStrummingPattern, OpenLyricSongWriteOptions, };
