import '../headless.ts';
import { type OpenLyricSong } from '../../plugins/OpenLyric/document/song-object.js';
import { type SongValidation } from './analysis.js';
/**
 * Writing a song: creating one, serializing a song object, importing a plain
 * chord sheet, and the structural edits the editor's preview offers — Config
 * fields, adding / renaming / deleting a section (keeping `Structure` in
 * step), replacing a section's lines, and Format. Every edit returns the new
 * text together with its validation, so a caller always knows whether it
 * produced a valid song.
 */
export interface SongEditResult {
    text: string;
    validation: SongValidation;
}
export interface CreateSongInput {
    title: string;
    subtitle?: string;
    description?: string | string[];
    artist?: string;
    copyright?: string;
    locales?: string[];
    key?: string;
    /** `72` or `72bpm`. */
    tempo?: string | number;
    time?: string;
    theme?: string;
    genre?: string;
    style?: string;
    /** Written as one comma-separated line. */
    keywords?: string[];
    /** `2024` or `"2024"`. */
    year?: string | number;
    /** The tune the lyrics are sung to. */
    melody?: string;
    attachments?: string[];
    strummingPatterns?: (string | {
        label?: string;
        pattern: string;
    })[];
    /** The compact performance order. Derived from `sections` when omitted. */
    structure?: string;
    /** Sections in written order. Default: one empty `Verse 1`. */
    sections?: {
        header: string;
        index?: number;
        lines?: string[];
    }[];
    /** Markdown above the fences — typically `# Title`. */
    preamble?: string;
}
/**
 * The Structure that plays `sections` once each, in order: `V1`, `C`, … with
 * adjacent repeats of one part merged into a repeat count (`Cx2`).
 */
export declare function deriveStructure(sections: readonly {
    header: string;
    index?: number;
}[]): string;
export declare function createSong(input: CreateSongInput): SongEditResult;
/** Serialize a song object (`schema.md` §8.2) and validate the notation. */
export declare function songFromObject(song: OpenLyricSong, { preamble }?: {
    preamble?: string;
}): SongEditResult;
export interface PlainTextImportResult extends SongEditResult {
    /** Whether the input looked like a chord sheet at all. */
    matchesPlainTextFormat: boolean;
    /** Sections renamed on the way in (labels from other chord-sheet formats). */
    renamedSections: {
        from: string;
        to: string;
    }[];
    /** Whether placeholders (title, structure …) had to be invented. */
    placeholdersUsed: boolean;
    hasConflictingDuplicates: boolean;
}
/**
 * Convert a plain chord sheet — title and metadata lines, `[Verse]`-style
 * labels, chord lines over lyric lines — into Open Lyric notation, the way the
 * editor's paste import does.
 */
export declare function importPlainText(rawText: string): PlainTextImportResult;
/**
 * Set, replace or (with an empty value) remove one Config field. A field the
 * fence does not declare yet is inserted at its canonical position. The
 * multiline fields take a list (one entry per line; `Strumming Patterns`
 * entries may be `{ label, pattern }`).
 */
export declare function setConfigField(text: string, field: string, value: unknown): SongEditResult & {
    field: string;
    action: 'set' | 'added' | 'removed' | 'unchanged';
};
export interface AddSectionInput {
    header: string;
    /**
     * For numbered types. Omitted: the first of a type is un-numbered (a verse
     * is `Verse 1`), later ones take the next free number.
     */
    index?: number;
    lines?: string[];
    /** Append the section's code to `Structure`. Default true. */
    appendToStructure?: boolean;
}
export declare function addSection(text: string, { header, index, lines, appendToStructure }: AddSectionInput): SongEditResult & {
    partName: string;
};
export declare function renameSection(text: string, from: string, to: string): SongEditResult & {
    partName: string;
    structureStepsUpdated: number;
};
export declare function deleteSection(text: string, partName: string): SongEditResult & {
    structureStepsRemoved: number;
};
/** Replace a section's body — every line between its fences. */
export declare function setSectionLines(text: string, partName: string, lines: readonly string[]): SongEditResult & {
    partName: string;
};
/** The section's body lines, as written. */
export declare function getSectionLines(text: string, partName: string): {
    partName: string;
    header: string;
    lines: string[];
    startLine: number;
    endLine: number;
};
/**
 * Said when a song declares Khmer: in the editor the km-KH plugin adds a
 * word-separator repair to Format that this language-neutral server has no
 * plugin for.
 */
export declare const KHMER_FORMAT_HINT = "The song's Locales include Khmer. In the editor, the km-KH plugin's Format also turns a space typed between Khmer letters into a zero-width word break (U+200B); no language plugin runs here, so that was not done. khmer-lint's fix_khmer with rules ['word-separator'] makes the same repair \u2014 but a visible space between Khmer phrases is also how a phrase ends, so review it before applying.";
/**
 * The editor's Format Document as it runs with no language plugin: per line,
 * repeated invisible characters collapsed and trailing whitespace removed.
 * (The word-separator repair a language plugin registers — Khmer's, from the
 * km-KH plugin — has no plugin to come from here; `hint` says so when the song
 * declares Khmer.)
 */
export declare function formatSong(text: string): SongEditResult & {
    changedLines: number;
    hint?: string;
};
/** One fix {@link applyFixes} made. */
export interface AppliedSongFix {
    /** The diagnostic it answered. */
    message: string;
    /** What it did, e.g. `Change to ol:Verse 2`. */
    title: string;
    /** 1-based line of the fixed range, in the text as it was when applied. */
    line: number;
    column: number;
}
/**
 * Apply every fix the validator knows — the `fix` each diagnostic of
 * {@link validateSong} may carry, the quick fixes the editor offers one at a
 * time — and validate again, until no diagnostic has one left (a corrected
 * fence header can let the next check through). Fixes whose ranges overlap
 * wait for the next pass. `applied` lists what was done; the diagnostics with
 * no known fix stay in `validation` for the caller to resolve.
 */
export declare function applyFixes(text: string): SongEditResult & {
    applied: AppliedSongFix[];
};
