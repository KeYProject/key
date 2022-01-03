package de.uka.ilkd.key.smt.st;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.smt.ModelExtractor;
import de.uka.ilkd.key.smt.SMTTranslator;
import de.uka.ilkd.key.smt.communication.*;
import de.uka.ilkd.key.smt.newsmt2.ModularSMTLib2Translator;

import javax.annotation.Nonnull;

public class MathSATSolverType extends AbstractSolverType {

    private static String NAME = "MathSAT";

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
        return "-input=smt2";
    }

    @Override
    public String getDefaultSolverCommand() {
        return "mathsat";
    }

    @Override
    public SMTTranslator createTranslator(Services services) {
        return new ModularSMTLib2Translator();
    }

    @Override
    public String[] getDelimiters() {
        return new String[] {"\n", "\r\n"};
    }

    @Override
    public boolean supportsIfThenElse() {
        return false;
    }

    @Override
    public String getVersionParameter() {
        return "-version";
    }

    @Override
    public String[] getSupportedVersions() {
        return new String[] {"none"};
    }

    @Nonnull
    @Override
    public AbstractSolverSocket getSocket(ModelExtractor query) {
        return new MathSATSocket(NAME, query);
    }

    @Override
    public @Nonnull
    SMTProcessLauncher getLauncher(SolverCommunication communication) {
        return new ExternalProcessLauncher(communication, getDelimiters());
    }

}
