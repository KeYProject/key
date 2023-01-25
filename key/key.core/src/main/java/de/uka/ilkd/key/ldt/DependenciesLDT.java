package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import org.key_project.util.ExtList;

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

public class DependenciesLDT extends LDT {

    public static final Name NAME = new Name("EventMarker");

    private final Function noR;
    private final Function noW;
    private final Function noRaW;
    private final Function noWaR;
    private final Function noWaW;

    private final Function noWAtHistory;
    private final Function noRAtHistory;
    private final Function noRaWAtHistory;
    private final Function noWaRAtHistory;
    private final Function noWaWAtHistory;

    private final Function relaxedNoRaW;
    private final Function relaxedNoWaR;
    private final Function relaxedNoWaW;

    private final Function rPred;
    private final Function wPred;
//    private final Function evPred;

    private final Function nothingMarker;
    private final Function readMarker;
    private final Function writeMarker;
    private final Function uniqueMarker;

    private final LocationVariable timestamp;


    public DependenciesLDT(TermServices services) {
        super(NAME, services);
        noR = addFunction(services, "noR");
        noW = addFunction(services, "noW");
        noRaW = addFunction(services, "noRaW");
        noWaR = addFunction(services, "noWaR");
        noWaW = addFunction(services, "noWaW");

        noWAtHistory = addFunction(services, "noWAtHistory");
        noRAtHistory = addFunction(services, "noRAtHistory");
        noRaWAtHistory = addFunction(services, "noRaWAtHistory");
        noWaRAtHistory = addFunction(services, "noWaRAtHistory");
        noWaWAtHistory = addFunction(services, "noWaWAtHistory");


        relaxedNoRaW = addFunction(services, "relaxedNoRaW");
        relaxedNoWaR = addFunction(services, "relaxedNoWaR");
        relaxedNoWaW = addFunction(services, "relaxedNoWaW");

        rPred = addFunction(services, "rPred");
        wPred = addFunction(services, "wPred");
//        evPred = addFunction(services, "evPred");

        readMarker = addFunction(services, "read");
        writeMarker = addFunction(services, "write");
        nothingMarker = addFunction(services, "nothing");
        uniqueMarker = addFunction(services, "unique");

        timestamp = (LocationVariable) services.getNamespaces().programVariables().lookup("timestamp");
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

//    public Function getEvPred() {
//        return evPred;
//    }


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
        return uniqueMarker;
    }

    public LocationVariable getTimestamp() {
        return timestamp;
    }

    @Override
    public boolean isResponsible(Operator op, Term[] subs, Services services, ExecutionContext ec) {
        return false;
    }

    @Override
    public boolean isResponsible(Operator op, Term left, Term right, Services services, ExecutionContext ec) {
        return false;
    }

    @Override
    public boolean isResponsible(Operator op, Term sub, TermServices services, ExecutionContext ec) {
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
        return functions().contains(op) && op != nothingMarker && op != readMarker && op != writeMarker && op != uniqueMarker;
    }

}
