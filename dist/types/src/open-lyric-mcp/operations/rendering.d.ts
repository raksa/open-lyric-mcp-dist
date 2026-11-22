import '../headless.ts';
/**
 * Rendering and exporting a song through the editor's own renderers: the
 * lyric view (the song in performance order), the markdown view (the whole
 * document with its fences as cards), plain text, a standalone HTML page, and
 * the DOCX / PowerPoint exports, and that PowerPoint deck as the one-file HTML
 * slide show the editor's "Download as HTML" writes. The decks are text slides
 * — the picture slides the editor can make need a live preview to photograph.
 */
export type SongTheme = 'light' | 'dark';
export type SongView = 'lyric' | 'markdown';
export interface SongViewOptions {
    /**
     * Render the song in this key: the notation is transposed first (needs a
     * Config `Key` of the same mode).
     */
    key?: string;
    /** Show chords as plain triads (`Cmaj7` → `C`). */
    simplifyChords?: boolean;
    /** Lyrics only: drop chord annotations (and chord-only lines). */
    hideChords?: boolean;
    /** Drop the bar marks that open lyric lines. */
    hideLeadingBars?: boolean;
    hideStrummingPatterns?: boolean;
    hideAttachments?: boolean;
    /** Show `//` comment lines. */
    showComments?: boolean;
    /**
     * Leave out the song notes the Structure does not place (`ol:Note` fences
     * it does not name), which otherwise follow the song.
     */
    hideNotes?: boolean;
    /** Lyric view and text only: just this section (`Chorus`, `Verse 2` …). */
    section?: string;
}
/** The song as plain text: title, meta line, structure, then each section. */
export declare function renderSongText(text: string, options?: SongViewOptions): string;
/** The lyric view's HTML fragment, static (style it with the preview stylesheet). */
export declare function renderSongLyricHtml(text: string, options?: SongViewOptions): string;
/** The markdown view's HTML fragment, static: the whole document, fences as cards. */
export declare function renderSongMarkdownHtml(text: string, options?: SongViewOptions): string;
export interface SongHtmlDocumentOptions extends SongViewOptions {
    view?: SongView;
    theme?: SongTheme;
    /**
     * The page's font, ahead of the system stack it falls back to. Named, so
     * it shows where the reader has it — unless `fontData` carries it.
     */
    fontFace?: string;
    /**
     * A TrueType font file the page declares under `fontFace` (`@font-face`,
     * the file written in), so it reads in that face on any computer: a
     * TrueType font of at most {@link SONG_EXPORT_FONT_MAX_BYTES} that its
     * maker lets be embedded (`OS/2` `fsType`), given with `fontFace`. Only
     * `docx`, `slideshow` and `html` exports take one.
     */
    fontData?: Uint8Array;
}
/** The largest font file an export carries, as the editor's Word export. */
export declare const SONG_EXPORT_FONT_MAX_BYTES: number;
/** A standalone HTML page — the chosen view with the preview styles inlined. */
export declare function renderSongHtmlDocument(text: string, { view, theme, fontFace, fontData, ...options }?: SongHtmlDocumentOptions): string;
export type SongRenderFormat = 'text' | 'lyric-html' | 'markdown-html' | 'html-document';
export declare function renderSong(text: string, format: SongRenderFormat, options?: SongHtmlDocumentOptions): string;
export type SongExportFormat = 'md' | 'json' | 'txt' | 'html' | 'docx' | 'pptx' | 'slideshow';
export declare const SONG_EXPORT_FORMATS: Readonly<Record<SongExportFormat, {
    extension: string;
    mimeType: string;
    binary: boolean;
}>>;
/** How a deck's lyrics sit across their box. */
export type SongDeckAlign = 'left' | 'center' | 'right';
export type SongDeckTransitionSpeed = 'slow' | 'medium' | 'fast';
/** The most lines of lyrics a deck slide holds, and the default. */
export declare const SONG_DECK_MAX_LINES_PER_SLIDE = 8;
/** The lyrics' size in points: the default and the range. */
export declare const SONG_DECK_FONT_SIZE: Readonly<{
    default: 24;
    min: 12;
    max: 96;
}>;
/** Every transition a deck can come on with: `none`, or one of the catalogue's. */
export declare const SONG_DECK_TRANSITIONS: readonly string[];
/**
 * The layout of the `pptx` and `slideshow` decks. Lyrics only unless
 * `hideChords: false`.
 */
export interface SongDeckOptions {
    /** The most lines of lyrics a slide holds, 1 to 8; default 8. */
    linesPerSlide?: number;
    /**
     * The deck's font, titles and lyrics alike. By default Arial, and Courier
     * New for the lyrics when chords are shown (their columns need it).
     */
    fontFace?: string;
    /** The lyrics' size in points, 12 to 96; default 24. */
    fontSize?: number;
    /** How the lyrics sit across their box; default `left`. */
    textAlign?: SongDeckAlign;
    /** How every slide comes on (`fade`, `push`, `morph` …); default `none`. */
    transition?: string;
    /** Default `medium`. */
    transitionSpeed?: SongDeckTransitionSpeed;
}
export interface SongExportOptions extends SongHtmlDocumentOptions, SongDeckOptions {
    format: SongExportFormat;
}
export interface SongExport {
    format: SongExportFormat;
    mimeType: string;
    /** A suggested file name, from the song's title. */
    fileName: string;
    /** Text formats are strings; DOCX and PPTX are bytes. */
    data: string | Uint8Array;
}
/**
 * A file-name stem from the song title: path-unsafe characters removed, and
 * the invisible ones — a Khmer title's zero-width word breaks (U+200B), ZWNJ,
 * ZWJ, word joiner, BOM — dropped, so the name is what it looks like.
 */
export declare function createSongFileStem(text: string): string;
export declare function exportSong(text: string, { format, theme, view, fontData: givenFontData, ...options }: SongExportOptions): Promise<SongExport>;
