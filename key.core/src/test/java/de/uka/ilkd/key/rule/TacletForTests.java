/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.io.File;
import java.nio.file.Path;
import java.nio.file.Paths;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.io.KeYFileForTests;
import de.uka.ilkd.key.proof.io.RuleSourceFactory;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.rules.RuleSet;
import org.key_project.util.collection.ImmutableSLList;

import static de.uka.ilkd.key.proof.io.RuleSource.ldtFile;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * this class is used to parse in Taclet from a file that are used by tests
 */
public class TacletForTests {

    private TacletForTests() {
    }

    public static final String testRules =
        HelperClassForTests.TESTCASE_DIRECTORY + File.separator + "testrules.key";
    public static String standardFile = testRules;

    public static AbbrevMap scm = new AbbrevMap();

    public static NamespaceSet nss = new NamespaceSet();
    public static TacletIndex rules = null;
    public static Services services;
    public static InitConfig initConfig;
    public static Path lastFile = null;

    private static Namespace<QuantifiableVariable> variables = null;
    private static Namespace<SchemaVariable> schemaVariables;

    public static final Profile profile = new JavaProfile() {
        // we do not want normal standard rules, but ruleSetsDeclarations is needed for string
        // library (HACK)
        @Override
        public RuleCollection getStandardRules() {
            return new RuleCollection(RuleSourceFactory.fromDefaultLocation(ldtFile),
                ImmutableSLList.nil());
        }
    };

    public static void clear() {
        lastFile = null;
        services = null;
        initConfig = null;
        rules = null;
        variables = null;
        scm = new AbbrevMap();
        nss = new NamespaceSet();
    }

    public static void parse(Path file) {
        try {
            if (!file.equals(lastFile)) {
                KeYFileForTests envInput = new KeYFileForTests("Test", file, profile);
                ProblemInitializer pi = new ProblemInitializer(envInput.getProfile());
                initConfig = pi.prepare(envInput);
                nss = initConfig.namespaces();
                rules = initConfig.createTacletIndex();
                services = initConfig.getServices();
                lastFile = file;
                variables = envInput.variables();
                schemaVariables = envInput.schemaVariables();
            }
        } catch (Exception e) {
            throw new RuntimeException("Exception occurred while parsing " + file, e);
        }
    }

    public static InitConfig initConfig() {
        if (initConfig == null) {
            parse();
        }
        return initConfig.deepCopy();
    }

    public static Services services() {
        if (services == null) {
            parse();
        }
        return services;
    }


    public static JavaInfo javaInfo() {
        return services().getJavaInfo();
    }

    public static JavaInfo getJavaInfo() {
        return javaInfo();
    }

    public static void setStandardFile(String filename) {
        standardFile = filename;
    }

    public static ProofAggregate problems() {
        return null;
    }

    public static void parse(String filename) {
        parse(Paths.get(filename));
    }

    public static void parse() {
        parse(standardFile);
    }

    public static NoPosTacletApp getTaclet(String name) {
        return rules.lookup(new Name(name));
    }

    public static AbbrevMap getAbbrevs() {
        return scm;
    }

    public static Namespace<Sort> getSorts() {
        return nss.sorts();
    }

    public static TacletIndex getRules() {
        return rules;
    }


    public static Namespace<RuleSet> getHeuristics() {
        return nss.ruleSets();
    }

    public static Namespace<? extends Function> getFunctions() {
        return nss.functions();
    }


    public static Namespace<QuantifiableVariable> getVariables() {
        return variables;
    }

    public static Namespace<SchemaVariable> getSchemaVariables() {
        return schemaVariables;
    }

    public static Namespace<IProgramVariable> getProgramVariables() {
        return nss.programVariables();
    }

    public static NamespaceSet getNamespaces() {
        return nss;
    }

    public static Function funcLookup(String name) {
        return getFunctions().lookup(new Name(name));
    }

    public static SchemaVariable svLookup(String name) {
        return getSchemaVariables().lookup(new Name(name));
    }

    public static Sort sortLookup(String name) {
        return getSorts().lookup(new Name(name));
    }

    public static JTerm parseTerm(String termstr, Services services) {
        if (termstr.isEmpty()) {
            return null;
        }

        try {
            KeyIO io = new KeyIO(services, nss);
            // TacletForTests.getAbbrevs()
            return io.parseExpression(termstr);
        } catch (Exception e) {
            fail("Exception occurred while parsing of " + termstr, e);
            return null;
        }

    }

    public static JTerm parseTerm(String termstr, NamespaceSet set) {
        if (termstr.isEmpty()) {
            return null;
        }
        return new KeyIO(services(), set).parseExpression(termstr);
    }

    public static JTerm parseTerm(String termstr) {
        return parseTerm(termstr, services());
    }

    public static ProgramElement parsePrg(String prgString) {
        Recoder2KeY r2k = new Recoder2KeY(services(), new NamespaceSet());
        return r2k.readBlockWithEmptyContext(prgString).program();
    }

    public static Goal createGoal() {
        return new Goal(new Node(new Proof("Some name", initConfig())),
            TacletIndexKit.getKit().createTacletIndex(),
            new BuiltInRuleAppIndex(new BuiltInRuleIndex()), services());
    }
}
