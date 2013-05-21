package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;

public final class MethodWellDefinedness extends WellDefinednessCheck {
    /* accessible-clause, assignable-clause, breaks-clause, callable-clause, captures-clause,
     * choice-statement, continues-clause, diverges-clause, duration-clause, if-statement,
     * measured-clause, returns-clause, when-clause, working-space-clause, requires-clause,
     * initially-clause, constraint, ensures-clause, signals-clause */
    static Type type;
    final Contract contract;

    public MethodWellDefinedness(Contract contract) {
        super(contract.getTarget());
        assert contract != null;
        this.contract = contract;
    }

    @Override
    public Type type() {
        return type;
    }

    @Override
    public int id() {
        return contract.id();
    }

    @Override
    public String getHTMLText(Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public String getPlainText(Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public boolean toBeSaved() {
        return false;
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
    public ProofOblInput createProofObl(InitConfig initConfig, Contract contract) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Contract setID(int newId) {
        return this;
    }    

    @Override
    public String getTypeName() {
        return "wellDefinedness_" + contract.getTypeName();
    }

    @Override
    public String getName() {
        return "wellDefinedness_" + contract.getName();
    }

    @Override
    public String getDisplayName() {
        return "wellDefinedness_" + contract.getDisplayName();
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
