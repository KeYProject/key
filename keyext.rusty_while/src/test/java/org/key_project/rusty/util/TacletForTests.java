package org.key_project.rusty.util;

import org.key_project.rusty.Services;
import org.key_project.rusty.logic.NamespaceSet;
import org.key_project.rusty.proof.init.*;
import org.key_project.rusty.proof.io.KeYFile;
import org.key_project.rusty.proof.io.RuleSourceFactory;
import org.key_project.util.collection.ImmutableSLList;

import java.io.File;

import static org.key_project.rusty.proof.io.RuleSource.LDT_FILE;

public class TacletForTests {

    private TacletForTests() {}

    public static final String testRules = TestHelper.TESTCASE_DIRECTORY + File.separator + "testrules.key";
    public static String standardFile = testRules;

    public static NamespaceSet nss = new NamespaceSet();
    //public static TacletIndex rules = null;
    public static Services services;
    public static InitConfig initConfig;
    public static File lastFile = null;

    //private static Namespace<QuantifiableVariable> variables = null;
    //private static Namespace<SchemaVariable> schemaVariables;

    public static final Profile profile = new RustProfile() {
        // we do not want normal standard rules, but ruleSetsDeclarations is needed for string
        // library (HACK)
        public RuleCollection getStandardRules() {
            return new RuleCollection(RuleSourceFactory.fromDefaultLocation(LDT_FILE),
                    ImmutableSLList.nil());
        }
    };

    public static void clear() {
        lastFile = null;
        services = null;
        initConfig = null;
        //rules = null;
        //variables = null;
        //scm = new AbbrevMap();
        nss = new NamespaceSet();
    }

    public static void parse() {
        parse(new File(standardFile));
    }

    public static void parse(File file) {
        try {
            if (!file.equals(lastFile)) {
                KeYFile envInput = new KeYFile("Test", file, profile);
                ProblemInitializer pi = new ProblemInitializer(envInput.getProfile());
                initConfig = pi.prepare(envInput);
                nss = initConfig.namespaces();
                //rules = initConfig.createTacletIndex();
                services = initConfig.getServices();
                lastFile = file;
                //variables = envInput.variables();
                //schemaVariables = envInput.schemaVariables();
            }
        } catch (Exception e) {
            throw new RuntimeException("Exception occurred while parsing " + file, e);
        }
    }

//    public static NoPosTacletApp getTaclet(String name) {
//        return rules.lookup(new Name(name));
//    }

    public static InitConfig initConfig() {
        if (initConfig == null) {
            parse();
        }
        //return initConfig.deepCopy();
        return initConfig;
    }

    public static Services services() {
        if (services == null) {
            parse();
        }
        return services;
    }


}
