package de.uka.ilkd.key.smt.st;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.smt.ModelExtractor;
import de.uka.ilkd.key.smt.SMTTranslator;
import de.uka.ilkd.key.smt.communication.AbstractSolverSocket;
import de.uka.ilkd.key.smt.communication.PrincessSocket;
import de.uka.ilkd.key.smt.newsmt2.ModularSMTLib2Translator;

import javax.annotation.Nonnull;

public class PrincessSolverType extends AbstractSolverType {

    private static String NAME = "Princess";

    @Override
    public String getName() {
        return NAME;
    }

    @Override
    public String getInfo() {
        return "";
    }

    @Override
    public String getDefaultSolverParameters() {
        return "+stdin";
    }

    @Override
    public String getDefaultSolverCommand() {
        return "princess";
    }

    @Override
    public SMTTranslator createTranslator(Services services) {
        return new ModularSMTLib2Translator();
    }

    @Override
    public String[] getDelimiters() {
        return new String[] {"\n", "\r"};
    }

    @Override
    public boolean supportsIfThenElse() {
        return true;
    }

    @Override
    public String getVersionParameter() {
        return "+version";
    }

    @Override
    public String[] getSupportedVersions() {
        return new String[] {"none"};
    }

    @Nonnull
    @Override
    public AbstractSolverSocket getSocket(ModelExtractor query) {
        return new PrincessSocket(NAME, query);
    }
}
