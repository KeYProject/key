package de.uka.ilkd.key.smt.st;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.smt.communication.AbstractSolverSocket;
import de.uka.ilkd.key.smt.communication.Z3Socket;
import de.uka.ilkd.key.smt.newsmt2.ModularSMTLib2Translator;

import javax.annotation.Nonnull;

/**
 * @author Alexander Weigl
 * @version 1 (9/29/21)
 */
public class Z3NewTLSolverType extends AbstractSolverType {

    @Override
    public String getDefaultSolverCommand() {
        return "z3";
    }

    @Override
    public String getDefaultSolverParameters() {
        return "-in -smt2";
    }

    @Override
    public SMTSolver createSolver(SMTProblem problem,
                                  SolverListener listener, Services services) {
        return new SMTSolverImplementation(problem, listener,
                services, this);
    }

    @Override
    public String getName() {
        return "Z3";
    }

    @Override
    public String getVersionParameter() {
        return "-version";
    }

    @Override
    public String getRawVersion() {
        final String tmp = super.getRawVersion();
        if (tmp == null) {
            return null;
        }
        return tmp.substring(tmp.indexOf("version"));
    }

    @Override
    public @Nonnull AbstractSolverSocket getSocket(ModelExtractor query) {
        return new Z3Socket(getName(), query);
    }

    @Override
    public String[] getSupportedVersions() {
        return new String[]{"version 3.2", "version 4.1", "version 4.3.0", "version 4.3.1", "version 4.8.8",
                "version 4.8.9", "version 4.8.10", "version 4.8.11", "version 4.8.12", "version 4.8.13",
                "version 4.8.14"};
    }

    @Override
    public String[] getDelimiters() {
        return new String[]{"\n", "\r"};
    }

    @Override
    public boolean supportsIfThenElse() {
        return true;
    }

    @Override
    public SMTTranslator createTranslator(Services services) {
        return new ModularSMTLib2Translator();
    }


    @Override
    public String getInfo() {
        return "";
//                    return "Z3 does not use quantifier elimination by default. This means for example that"
//                                    + " the following problem cannot be solved automatically by default:\n\n"
//                                    + "\\functions{\n"
//                                    + "\tint n;\n"
//                                    + "}\n\n"
//                                    + "\\problem{\n"
//                                    + "\t((\\forall int x;(x<=0 | x >= n+1)) & n >= 1)->false\n"
//                                    + "}"
//                                    + "\n\n"
//                                    + "You can activate quantifier elimination by appending QUANT_FM=true to"
//                                    + " the execution command."
    }
}
