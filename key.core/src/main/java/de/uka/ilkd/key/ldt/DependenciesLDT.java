/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;

import org.key_project.util.ExtList;

public class DependenciesLDT extends LDT {

    public static final Name NAME = new Name("EventMarker");

    private final Function noR;
    private final Function noW;
    private final Function noRaW;
    private final Function noWaR;
    private final Function noWaW;

    private final Function relaxedNoR;
    private final Function relaxedNoW;
    private final Function relaxedNoRaW;
    private final Function relaxedNoWaR;
    private final Function relaxedNoWaW;

    private final Function rPred;
    private final Function wPred;
    private final Function relaxedRPred;
    private final Function relaxedWPred;

    private final Function nothingMarker;
    private final Function readMarker;
    private final Function writeMarker;
    private final Function startMarker;

    private final Function endMarker;

    private final LocationVariable timestamp;
    private final Function noWaWAtHistory;
    private final Function noRaWAtHistory;
    private final Function noWaRAtHistory;
    private final Function noWAtHistory;
    private final Function noRAtHistory;

    public Function getNoWaWAtHistory() {
        return noWaWAtHistory;
    }

    public Function getNoRaWAtHistory() {
        return noRaWAtHistory;
    }

    public Function getNoWaRAtHistory() {
        return noWaRAtHistory;
    }

    public Function getNoWAtHistory() {
        return noWAtHistory;
    }

    public Function getNoRAtHistory() {
        return noRAtHistory;
    }

    public DependenciesLDT(TermServices services) {
        super(NAME, services);
        noR = addFunction(services, "noR");
        noW = addFunction(services, "noW");
        noRaW = addFunction(services, "noRaW");
        noWaR = addFunction(services, "noWaR");
        noWaW = addFunction(services, "noWaW");

        relaxedNoR = addFunction(services, "relaxedNoR");
        relaxedNoW = addFunction(services, "relaxedNoW");
        relaxedNoRaW = addFunction(services, "relaxedNoRaW");
        relaxedNoWaR = addFunction(services, "relaxedNoWaR");
        relaxedNoWaW = addFunction(services, "relaxedNoWaW");

        noRAtHistory = addFunction(services, "noRAtHistory");
        noWAtHistory = addFunction(services, "noWAtHistory");
        noRaWAtHistory = addFunction(services, "noRaWAtHistory");
        noWaRAtHistory = addFunction(services, "noWaRAtHistory");
        noWaWAtHistory = addFunction(services, "noWaWAtHistory");

        rPred = addFunction(services, "rPred");
        wPred = addFunction(services, "wPred");
        relaxedRPred = addFunction(services, "relaxedRPred");
        relaxedWPred = addFunction(services, "relaxedWPred");

        readMarker = addFunction(services, "read");
        writeMarker = addFunction(services, "write");
        nothingMarker = addFunction(services, "nothing");
        startMarker = addFunction(services, "start");
        endMarker = addFunction(services, "end");

        timestamp =
            (LocationVariable) services.getNamespaces().programVariables().lookup("timestamp");
        if (timestamp == null)
            throw new RuntimeException("LDT: Program variable timestamp not found.\n" +
                "It seems that there are definitions missing from the .key files.");

    }

    public Function getNoR() {
        return noR;
    }

    public Function getNoW() {
        return noW;
    }

    public Function getNoRaW() {
        return noRaW;
    }

    public Function getNoWaR() {
        return noWaR;
    }

    public Function getNoWaW() {
        return noWaW;
    }

    public Function getRelaxedNoR() {
        return relaxedNoR;
    }

    public Function getRelaxedNoW() {
        return relaxedNoW;
    }

    public Function getRelaxedNoRaW() {
        return relaxedNoRaW;
    }

    public Function getRelaxedNoWaR() {
        return relaxedNoWaR;
    }

    public Function getRelaxedNoWaW() {
        return relaxedNoWaW;
    }

    public Function getRPred() {
        return rPred;
    }

    public Function getWPred() {
        return wPred;
    }

    public Function getRelaxedRPred() {
        return relaxedRPred;
    }

    public Function getRelaxedWPred() {
        return relaxedWPred;
    }

    // public Function getEvPred() {
    // return evPred;
    // }


    public Function getNothingMarker() {
        return nothingMarker;
    }

    public Function getReadMarker() {
        return readMarker;
    }

    public Function getWriteMarker() {
        return writeMarker;
    }


    public Function getUniqueMarker() {
        return startMarker;
    }

    public Function getEndMarker() {
        return endMarker;
    }

    public LocationVariable getTimestamp() {
        return timestamp;
    }

    @Override
    public boolean isResponsible(Operator op, Term[] subs, Services services, ExecutionContext ec) {
        return false;
    }

    @Override
    public boolean isResponsible(Operator op, Term left, Term right, Services services,
            ExecutionContext ec) {
        return false;
    }

    @Override
    public boolean isResponsible(Operator op, Term sub, TermServices services,
            ExecutionContext ec) {
        return false;
    }

    @Override
    public Term translateLiteral(Literal lit, Services services) {
        assert false;
        return null;
    }

    @Override
    public Function getFunctionFor(Operator op, Services services, ExecutionContext ec) {
        assert false;
        return null;
    }

    @Override
    public boolean hasLiteralFunction(Function f) {
        assert false;
        return false;
    }

    @Override
    public Expression translateTerm(Term t, ExtList children, Services services) {
        assert false;
        return null;
    }

    @Override
    public Type getType(Term t) {
        assert false;
        return null;
    }

    public boolean isDependencePredicate(de.uka.ilkd.key.logic.op.Operator op) {
        return functions().contains(op) && op != nothingMarker && op != readMarker
                && op != writeMarker && op != startMarker && op != endMarker;
    }

    public boolean isHistoryPredicate(de.uka.ilkd.key.logic.op.Operator op) {
        return op == this.noRAtHistory || op == this.noWAtHistory ||
                op == this.noRaWAtHistory || op == this.noWaRAtHistory || op == this.noWaWAtHistory;
    }

    public boolean isRelaxedDependencePred(de.uka.ilkd.key.logic.op.Operator op) {
        return op == this.relaxedNoW || op == this.relaxedNoR ||
                op == this.relaxedNoRaW || op == this.relaxedNoWaR || op == this.relaxedNoWaW;
    }
}
