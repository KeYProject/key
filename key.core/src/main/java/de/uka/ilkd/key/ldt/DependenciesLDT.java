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
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;

import org.key_project.logic.Name;
import org.key_project.util.ExtList;

public class DependenciesLDT extends LDT {

    public static final Name NAME = new Name("EventMarker");

    private final JFunction noR;
    private final JFunction noW;
    private final JFunction noRaW;
    private final JFunction noWaR;
    private final JFunction noWaW;

    private final JFunction relaxedNoR;
    private final JFunction relaxedNoW;
    private final JFunction relaxedNoRaW;
    private final JFunction relaxedNoWaR;
    private final JFunction relaxedNoWaW;

    private final JFunction rPred;
    private final JFunction wPred;
    private final JFunction relaxedRPred;
    private final JFunction relaxedWPred;

    private final JFunction nothingMarker;
    private final JFunction readMarker;
    private final JFunction writeMarker;
    private final JFunction startMarker;

    private final JFunction endMarker;

    private final LocationVariable timestamp;
    private final JFunction noWaWAtHistory;
    private final JFunction noRaWAtHistory;
    private final JFunction noWaRAtHistory;
    private final JFunction noWAtHistory;
    private final JFunction noRAtHistory;

    public JFunction getNoWaWAtHistory() {
        return noWaWAtHistory;
    }

    public JFunction getNoRaWAtHistory() {
        return noRaWAtHistory;
    }

    public JFunction getNoWaRAtHistory() {
        return noWaRAtHistory;
    }

    public JFunction getNoWAtHistory() {
        return noWAtHistory;
    }

    public JFunction getNoRAtHistory() {
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

    public JFunction getNoR() {
        return noR;
    }

    public JFunction getNoW() {
        return noW;
    }

    public JFunction getNoRaW() {
        return noRaW;
    }

    public JFunction getNoWaR() {
        return noWaR;
    }

    public JFunction getNoWaW() {
        return noWaW;
    }

    public JFunction getRelaxedNoR() {
        return relaxedNoR;
    }

    public JFunction getRelaxedNoW() {
        return relaxedNoW;
    }

    public JFunction getRelaxedNoRaW() {
        return relaxedNoRaW;
    }

    public JFunction getRelaxedNoWaR() {
        return relaxedNoWaR;
    }

    public JFunction getRelaxedNoWaW() {
        return relaxedNoWaW;
    }

    public JFunction getRPred() {
        return rPred;
    }

    public JFunction getWPred() {
        return wPred;
    }

    public JFunction getRelaxedRPred() {
        return relaxedRPred;
    }

    public JFunction getRelaxedWPred() {
        return relaxedWPred;
    }

    // public JFunction getEvPred() {
    // return evPred;
    // }


    public JFunction getNothingMarker() {
        return nothingMarker;
    }

    public JFunction getReadMarker() {
        return readMarker;
    }

    public JFunction getWriteMarker() {
        return writeMarker;
    }


    public JFunction getUniqueMarker() {
        return startMarker;
    }

    public JFunction getEndMarker() {
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
    public JFunction getFunctionFor(Operator op, Services services, ExecutionContext ec) {
        assert false;
        return null;
    }

    @Override
    public boolean hasLiteralFunction(JFunction f) {
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
