package de.uka.ilkd.key.smt.st;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.smt.communication.AbstractSolverSocket;
import de.uka.ilkd.key.smt.communication.Z3CESocket;

import javax.annotation.Nonnull;

/**
 * @author Alexander Weigl
 * @version 1 (9/29/21)
 */
public class Z3CounterExampleSolverType extends AbstractSolverType {
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
        return "Z3_CE";
    }

    @Override
    public String getVersionParameter() {
        return "-version";
    }

    @Override
    public String[] getSupportedVersions() {
        return new String[]{"version 4.3.1"};
    }

    @Override
    public @Nonnull AbstractSolverSocket getSocket(ModelExtractor query) {
        return new Z3CESocket(getName(), query);
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
        return new SmtLib2Translator(services,
                new AbstractSMTTranslator.Configuration(false, false));
    }


    @Override
    public String getInfo() {
        return "";
        //                        return "Z3 does not use quantifier elimination by default. This means for example that"
        //                                        + " the following problem cannot be solved automatically by default:\n\n"
        //                                        + "\\functions{\n"
        //                                        + "\tint n;\n"
        //                                        + "}\n\n"
        //                                        + "\\problem{\n"
        //                                        + "\t((\\forall int x;(x<=0 | x >= n+1)) & n >= 1)->false\n"
        //                                        + "}"
        //                                        + "\n\n"
        //                                        + "You can activate quantifier elimination by appending QUANT_FM=true to"
        //                                        + " the execution command.";
    }


}
