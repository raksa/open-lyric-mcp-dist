import '../headless.ts';
import { createSvguitarData } from '../../plugins/OpenLyric/domain/chord-voicings.js';
export interface SongTransposeOptions {
    /** The key to move to — one of the Config `Key` values. */
    toKey?: string;
    /** Or a number of semitones (negative goes down). Ignored when `toKey` is set. */
    semitones?: number;
}
export interface SongTransposeResult {
    text: string;
    fromKey: string;
    toKey: string;
    semitones: number;
    changedLines: number;
}
export declare function transposeSong(text: string, options: SongTransposeOptions): SongTransposeResult;
export interface ChordTransposeResult {
    chord: string;
    transposed: string;
    semitones: number;
}
export declare function transposeChord(chord: string, { semitones, fromKey, toKey, }: {
    semitones?: number;
    fromKey?: string;
    toKey?: string;
}): ChordTransposeResult;
export interface KeyChordsResult {
    key: string;
    tonic: string;
    mode: 'major' | 'minor';
    diatonicTriads: string[];
    /** Every Config `Key` value, as the transposition targets. */
    keys: string[];
}
export declare function getKeyChords(keyText: string): KeyChordsResult;
export type ChordInstrument = 'guitar' | 'ukulele';
export interface ChordVoicing {
    /** One fret per string, lowest string first: -1 muted, 0 open, relative to baseFret. */
    frets: number[];
    fingers: number[];
    baseFret: number;
    barres: number[];
    capo: boolean;
    midi: number[];
}
export interface ChordDescription {
    chord: string;
    valid: boolean;
    name: string;
    simplified: string;
    degreeHints: string[];
    instrument: ChordInstrument;
    /** The database family the voicings come from (`C` + `major` …), when found. */
    matched?: {
        root: string;
        suffix: string;
    };
    /** Easiest first. */
    voicings: ChordVoicing[];
    /** SVGuitar data for the easiest voicing. */
    diagram?: ReturnType<typeof createSvguitarData>;
}
export declare function describeChord(chord: string, { instrument, limit, }?: {
    instrument?: ChordInstrument;
    limit?: number;
}): Promise<ChordDescription>;
