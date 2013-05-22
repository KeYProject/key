package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.pp.LogicPrinter;

public final class MethodWellDefinedness extends WellDefinednessCheck {
    /* accessible-clause, assignable-clause, breaks-clause, callable-clause, captures-clause,
     * choice-statement, continues-clause, diverges-clause, duration-clause, if-statement,
     * measured-clause, returns-clause, when-clause, working-space-clause, requires-clause,
     * initially-clause, constraint, ensures-clause, signals-clause */
    final Contract contract;

    public MethodWellDefinedness(Contract contract, Services services) {
        super(contract.getTarget(), Type.METHOD_CONTRACT);
        assert contract != null;
        this.contract = contract;
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final LocationVariable baseHeap = heapLDT.getHeap();
        this.ensures = contract.getRequires(baseHeap);
        this.assignable = contract.getAssignable(baseHeap);
    }

    @Override
    public Type type() {
        return Type.METHOD_CONTRACT;
    }

    @Override
    public int id() {
        return contract.id();
    }

    @Override
    public String getHTMLText(Services services) {
        return getText(true, services);
    }

    @Override
    public String getPlainText(Services services) {
        return getText(false, services);
    }

    private String getText(boolean includeHtmlMarkup, Services services) {
        String mods = "";
        if (getAssignable(null) != null) {
            String printMods = LogicPrinter.quickPrintTerm(getAssignable(null), services);
            mods = mods
                    + (includeHtmlMarkup ? "<br><b>" : "\n")
                    + "mod"
                    + (includeHtmlMarkup ? "</b> " : ": ")
                    + (includeHtmlMarkup ?
                            LogicPrinter.escapeHTML(printMods, false) : printMods.trim());
        }

        String pres = "";
        if (getRequires(null) != null) {
            String printPres = LogicPrinter.quickPrintTerm(getRequires(null), services);
            pres = pres
                    + (includeHtmlMarkup ? "<br><b>" : "\n")
                    + "pre"
                    + (includeHtmlMarkup ? "</b> " : ": ")
                    + (includeHtmlMarkup ?
                            LogicPrinter.escapeHTML(printPres, false) : printPres.trim());
        }

        if (includeHtmlMarkup) {
           return "<html>"
                 + pres
                 + mods +
                 "</html>";
        }
        else {
           return pres
                 + mods;
        }
     }

    @Override
    public boolean transactionApplicableContract() {
        return contract.transactionApplicableContract();
    }

    @Override
    public String proofToString(Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Contract setID(int newId) {
        return this;
    }    

    @Override
    public String getTypeName() {
        return "Well-Definedness of " + contract.getTypeName();
    }

    @Override
    public String getName() {
        return "Well-Definedness of " + contract.getName();
    }

    @Override
    public VisibilityModifier getVisibility() {
        return contract.getVisibility();
    }

    @Override
    public KeYJavaType getKJT() {
        return contract.getKJT();
    }

}
