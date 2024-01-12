/**
 * This package provides the functionalities of parsing JML comments into KeY constructs.
 * {@link de.uka.ilkd.key.speclang.njml.JmlIO} is the entry facade for the end-developer.
 * <p>
 * The main translation happens (due to legacy restriction) in two step: First the given comments
 * are parsed and wrapped into {@code TextualJML*} part. Second these are interpreted and attached
 * to the {@link de.uka.ilkd.key.proof.mgt.SpecificationRepository} This process happens in the
 * legacy package {@link de.uka.ilkd.key.speclang.jml}.
 * <p>
 * The translation happens in {@link de.uka.ilkd.key.speclang.njml.TextualTranslator} and
 * {@link de.uka.ilkd.key.speclang.njml.Translator}.
 * <p>
 * Gradle has a task for debugging the lexer {@code gradle debugJmlLexer}.
 *
 * @author Alexander Weigl
 * @version 1 (6/2/21)
 */
package de.uka.ilkd.key.speclang.njml;
