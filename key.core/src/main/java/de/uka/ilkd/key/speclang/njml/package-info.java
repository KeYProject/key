/**
 * This package provides the functionalities of parsing and translating JML
 * comments into KeY constructs.
 * {@link de.uka.ilkd.key.speclang.njml.JmlIO} is the entry facade for the
 * end-developer.
 * <p>
 * JML is parsed by JMLtk together with the surrounding Java file and consumed
 * by the KeY front-end as {@link de.uka.ilkd.key.speclang.jml.JmlSpec}s. For
 * the translation, the constructs are re-serialized against KeY's own JML
 * grammar ({@code JmlParser.g4}, see
 * {@code de.uka.ilkd.key.speclang.jml.translation.JmlToTextual}) and the
 * resulting parse trees are interpreted by {@link
 * de.uka.ilkd.key.speclang.njml.Translator} into KeY terms (see {@link
 * de.uka.ilkd.key.speclang.njml.JmlTermFactory}).
 * <p>
 * Gradle has a task for debugging the lexer {@code gradle debugJmlLexer}.
 *
 * @author Alexander Weigl
 * @version 1 (6/2/21)
 */
package de.uka.ilkd.key.speclang.njml;
