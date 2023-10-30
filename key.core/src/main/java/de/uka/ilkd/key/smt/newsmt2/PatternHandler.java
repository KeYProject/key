/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
// package de.uka.ilkd.key.smt.newsmt2;
//
// import de.uka.ilkd.key.java.Services;
// import de.uka.ilkd.key.ldt.LocSetLDT;
// import de.uka.ilkd.key.logic.Name;
// import de.uka.ilkd.key.logic.Term;
// import de.uka.ilkd.key.logic.op.Function;
// import de.uka.ilkd.key.logic.op.Operator;
// import de.uka.ilkd.key.logic.op.SortDependingFunction;
// import de.uka.ilkd.key.logic.sort.GenericSort;
// import de.uka.ilkd.key.logic.sort.Sort;
// import de.uka.ilkd.key.smt.SMTTranslationException;
// import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;
//
// @Deprecated
// public class PatternHandler implements SMTHandler {
//
// public static final SortDependingFunction PATTERN_FUNCTION = makePatternFunction();
// public static final Function FORMULA_PATTERN_FUNCTION = makeFormulaPatternFunction();
// public static final Function SMT_PATTERN_FUNCTION = makeSMTPatternFunction();
//
// private static final String PATTERN_NAME = "PATTERN";
// private static final String FORMULA_PATTERN_NAME = "FPATTERN";
// private static final String SMT_PATTERN_NAME = "SMT_PATTERN";
//
// private static Function makeSMTPatternFunction() {
// Sort[] argSorts = { Sort.FORMULA, Sort.ANY };
// return new Function(new Name(SMT_PATTERN_NAME), Sort.FORMULA, argSorts);
// }
//
// private static Function makeFormulaPatternFunction() {
// Sort[] argSorts = { Sort.FORMULA };
// return new Function(new Name(FORMULA_PATTERN_NAME), Sort.FORMULA, argSorts);
// }
//
// private static SortDependingFunction makePatternFunction() {
// GenericSort g = new GenericSort(new Name("G"));
// Sort[] argSorts = { g };
// return SortDependingFunction.createFirstInstance(g, new Name(PATTERN_NAME), g, argSorts, false);
// }
//
// @Override
// public void init(MasterHandler masterHandler, Services services) {
// }
//
// @Override
// public boolean canHandle(Term term) {
// Operator op = term.op();
// if (op == FORMULA_PATTERN_FUNCTION || op == SMT_PATTERN_FUNCTION) {
// return true;
// }
//
// if (op instanceof SortDependingFunction) {
// SortDependingFunction sdf = (SortDependingFunction) op;
// return PATTERN_FUNCTION.isSimilar(sdf);
// }
//
// return false;
// }
//
// @Override
// public SExpr handle(MasterHandler trans, Term term) {
// if (term.op() == SMT_PATTERN_FUNCTION) {
// return SExprs.patternSExpr(trans.translate(term.sub(0)), new
// SExpr(trans.translate(term.sub(1))));
// } else {
// return SExprs.patternSExpr(trans.translate(term.sub(0)), new
// SExpr(trans.translate(term.sub(0))));
// }
// }
// }
