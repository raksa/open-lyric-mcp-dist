import '../headless.ts';
import { type OpenLyricSongStrummingPattern } from '../../plugins/OpenLyric/document/song-object.js';
/**
 * Reading a song: validation, its sections, its structure, its chords and
 * its Config — all from the document text, through the editor's own parser
 * and validator.
 */
export type SongDiagnosticSeverity = 'error' | 'warning' | 'information' | 'hint';
export interface SongDiagnostic {
    message: string;
    severity: SongDiagnosticSeverity;
    /** 1-based line of the first character. */
    line: number;
    /** 1-based column of the first character. */
    column: number;
    endLine: number;
    /** 1-based column just past the last character. */
    endColumn: number;
    /** The fix, when the validator knows it: `text` in place of the range. */
    fix?: {
        title: string;
        text: string;
    };
}
export interface SongValidation {
    valid: boolean;
    errorCount: number;
    warningCount: number;
    diagnostics: SongDiagnostic[];
}
export declare function validateSong(text: string): SongValidation;
/** A one-paragraph, human-readable account of a validation result. */
export declare function summarizeValidation(validation: SongValidation): string;
export interface SongSectionInfo {
    partName: string;
    header: string;
    index?: number;
    kind: string;
    /** 1-based line of the ```` ```ol: ```` opening line. */
    startLine: number;
    /** 1-based line of the closing ```` ``` ````. */
    endLine: number;
    /** Body lines between the fences. */
    lineCount: number;
    /** Whether `Structure` names this part. */
    inStructure: boolean;
}
export interface StructureStepInfo {
    code: string;
    partName: string;
    repeat: number;
    label: string;
    declared?: boolean;
}
export interface StructureInfo {
    text: string;
    error: string | null;
    steps: StructureStepInfo[];
    /** Parts the structure names that no fence declares. */
    undeclaredParts: string[];
    /** Declared sections the structure never plays. */
    unusedSections: string[];
}
/**
 * Read a `Structure` value — the compact performance order — step by step.
 * With `declaredPartNames`, each step says whether a fence declares its part
 * and the result lists what is missing and what is unused.
 */
export declare function describeStructure(structure: string, declaredPartNames?: readonly string[]): StructureInfo;
export declare function listSongSections(text: string): SongSectionInfo[];
export interface SongChordInfo {
    chord: string;
    name: string;
    simplified: string;
    degreeHints: string[];
    /** Whether the chord (or its simplified triad) is diatonic to the song's key. */
    inKey?: boolean;
}
export interface SongChordsInfo {
    key: string;
    diatonicTriads: string[];
    chords: SongChordInfo[];
}
export declare function listSongChords(text: string): SongChordsInfo;
export interface SongInfo {
    hasConfig: boolean;
    title: string;
    subtitle?: string;
    artist?: string;
    copyright?: string;
    description: string[];
    locales: string[];
    key?: string;
    tempo?: string;
    time?: string;
    theme?: string;
    genre?: string;
    style?: string;
    keywords: string[];
    year?: string;
    melody?: string;
    structure: StructureInfo;
    sections: SongSectionInfo[];
    chords: string[];
    attachments: {
        title: string;
        type: string;
        link: string;
    }[];
    strummingPatterns: OpenLyricSongStrummingPattern[];
    /** What the song object could not carry (comments, unknown fields …). */
    warnings: string[];
}
export declare function getSongInfo(text: string): SongInfo;
