/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
// package de.uka.ilkd.key.smt.newsmt2;
//
// import de.uka.ilkd.key.java.Services;
// import de.uka.ilkd.key.logic.Name;
// import de.uka.ilkd.key.logic.Term;
// import de.uka.ilkd.key.logic.op.Operator;
// import de.uka.ilkd.key.logic.op.SortDependingFunction;
// import de.uka.ilkd.key.logic.sort.Sort;
// import de.uka.ilkd.key.smt.SMTTranslationException;
// import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;
// import de.uka.ilkd.key.util.Pair;
//
// import java.util.HashMap;
// import java.util.Map;
// import java.util.Properties;
//
/// **
// * This abstract handler handles a collection of function symbols.
// *
// * The supported functions can be registered in the overridden {@link
// * SMTHandler#init(MasterHandler, Services, Properties)} function.
// *
// * It supports function symbols and sort-depending functions with casting. (i.e.
// * X::f(y) will be translated as(X)any::f(y)).
// *
// * The declarations and axioms must still be collected in the corresponding xml
// * preamble files.
// *
// * @author Mattias Ulbrich
// */
// public abstract class SMTFunctionsHandler implements SMTHandler {
//
// /**
// * all fixed-sort operators supported by this collection.
// */
// private Map<Operator, Pair<String, Type>> supportedOperators = new HashMap<>();
//
// /**
// * all supported sort-depending operators. The "any" instances are stored here.
// */
// private Map<Name, String> supportedCastingOperators = new HashMap<>();
//
// /**
// * services obtained in {@link SMTHandler#init(MasterHandler, Services, Properties)}
// */
// protected Services services;
//
// /**
// * Can be and should be overridden in subclasses
// * @param masterHandler
// * @param services the non-null services object which is relevant for
// * @param handlerSnippets
// */
// @Override
// public void init(MasterHandler masterHandler, Services services, Properties handlerSnippets) {
// this.services = services;
// }
//
// /**
// * Add an operator to the supported set. The name of the translation
// * is the name of the operator itself.
// *
// * @param op a non-null operator
// */
// protected void addOperator(Operator op) {
// addOperator(op, op.name().toString());
// }
//
// /**
// * Add an operator to the supported set. The name is explicitly fiven
// *
// * @param op a non-null operator
// * @param name the name to be used in SMT
// */
// protected void addOperator(Operator op, String name) {
// addOperator(op, name, Type.UNIVERSE);
// }
//
// /**
// * Add an operator to the supported set. The given type is used as coercion
// * @param op
// * @param type
// */
// protected void addOperator(Operator op, Type type) {
// addOperator(op, op.name().toString(), type);
// }
//
// private void addOperator(Operator op, String name, Type type) {
// supportedOperators.put(op, new Pair<>(name, type));
// }
//
// protected void addCastingOperator(SortDependingFunction op, String name) {
// supportedCastingOperators.put(op.getKind(), name);
// }
//
// protected void addCastingOperator(SortDependingFunction op) {
// addCastingOperator(op, op.getKind().toString());
// }
//
// @Override
// public boolean canHandle(Operator op) {
// if(op instanceof SortDependingFunction) {
// return supportedCastingOperators.containsKey(((SortDependingFunction) op).getKind());
// } else {
// return supportedOperators.containsKey(op);
// }
// }
//
// @Override
// public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
// Operator op = term.op();
//
// if(op instanceof SortDependingFunction) {
// SortDependingFunction sdf = (SortDependingFunction) op;
// String name = supportedCastingOperators.get(sdf.getKind());
// trans.addFromSnippets(name);
// SExpr result = trans.handleAsFunctionCall(name, term);
// Sort dep = sdf.getSortDependingOn();
// if (dep == Sort.ANY) {
// return result;
// } else {
// return SExprs.castExpr(SExprs.sortExpr(dep), result);
// }
// }
//
// Pair<String, Type> entry = supportedOperators.get(op);
// if (entry != null) {
// trans.addFromSnippets(entry.first);
// return trans.handleAsFunctionCall(entry.first, entry.second, term);
// }
//
// throw new SMTTranslationException("Unsupported term: " + term);
// }
//
// }
