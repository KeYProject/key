/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.io.File;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.io.KeYFileForTests;
import de.uka.ilkd.key.proof.io.RuleSourceFactory;
import de.uka.ilkd.key.util.HelperClassForTests;

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
    public static File lastFile = null;

    private static Namespace<QuantifiableVariable> variables = null;
    private static Namespace<SchemaVariable> schemaVariables;

    public static final Profile profile = new JavaProfile() {
        // we do not want normal standard rules, but ruleSetsDeclarations is needed for string
        // library (HACK)
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

    public static void parse(File file) {
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
        parse(new File(filename));
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

    public static Namespace<Function> getFunctions() {
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

    public static Term parseTerm(String termstr, Services services) {
        if (termstr.equals("")) {
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

    public static Term parseTerm(String termstr, NamespaceSet set) {
        if (termstr.equals("")) {
            return null;
        }
        return new KeyIO(services(), set).parseExpression(termstr);
    }

    public static Term parseTerm(String termstr) {
        return parseTerm(termstr, services());
    }

    public static ProgramElement parsePrg(String prgString) {
        Recoder2KeY r2k = new Recoder2KeY(services(), new NamespaceSet());
        return r2k.readBlockWithEmptyContext(prgString).program();
    }
}
