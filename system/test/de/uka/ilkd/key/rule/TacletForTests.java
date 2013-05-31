// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


/** this class is used to parse in Taclet from a file that are used by tests */
package de.uka.ilkd.key.rule;

import java.io.File;
import java.io.StringReader;

import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.KeYLexer;
import de.uka.ilkd.key.parser.KeYParser;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.io.KeYFileForTests;
import de.uka.ilkd.key.proof.io.RuleSource;

public class TacletForTests {

    private TacletForTests() {}

    public static final String testRules = System.getProperty("key.home")+
        File.separator+"examples"+
        File.separator+"_testcase"+
        File.separator+"testrules.key";
    public static String standardFile = testRules;
    
    public static AbbrevMap scm = new AbbrevMap();
    
    public static NamespaceSet nss = new NamespaceSet();
    public static TacletIndex rules= null;
    public static Services services;
    public static File lastFile=null;
    
    public static Namespace variables = null;

    public static Profile profile = new JavaProfile() {
            //we do not want normal standard rules, but ruleSetsDeclarations is needed for string library (HACK)
            public RuleCollection getStandardRules() {
                return new RuleCollection(
                                RuleSource.initRuleFile("LDTsForTestsOnly.key"), 
                                ImmutableSLList.<BuiltInRule>nil());
            }
        };
        
    public static void clear() {
        lastFile = null;
        services = null;
        rules = null;
        variables = null;
        scm = new AbbrevMap();
        nss = new NamespaceSet();        
    }
        
    public static void parse(File file) {
	try {	    
	    if (!file.equals(lastFile)) {
		KeYFileForTests envInput = new KeYFileForTests("Test", file);	
		ProblemInitializer pi = new ProblemInitializer(profile); 
		InitConfig ic = pi.prepare(envInput);
              	nss      = ic.namespaces(); 
                rules    = ic.createTacletIndex();
                services = ic.getServices();
		lastFile = file;
		variables = envInput.variables();
	    }
	} catch (Exception e) {
	    System.err.println("Exception occurred while parsing "+file+"\n");
	    e.printStackTrace();
	    System.exit(-1);
	}
    }

    public static Services services() {
	if (services == null) parse();
	return services;
    }

    public static JavaInfo javaInfo() {
	return services ().getJavaInfo ();
    }

    public static JavaInfo getJavaInfo() {
	return javaInfo();
    }

    public static void setStandardFile(String filename) {
	standardFile=filename;
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
    
    public static AbbrevMap getAbbrevs(){
        return scm;
    }

    public static Namespace getSorts() {
	return nss.sorts();
    }

    public static TacletIndex getRules() {
	return rules;
    }


    public static Namespace getHeuristics() {
	return nss.ruleSets();
    }

    public static Namespace getFunctions() {
	return nss.functions();
    }


    public static Namespace getVariables() {
	return variables;
    }

    public static Namespace getProgramVariables() {
	return nss.programVariables();
    }

    public static NamespaceSet getNamespaces() {
	return nss;
    }

    public static Function funcLookup(String name) {
	return (Function)getFunctions().lookup(new Name(name));
    }

    public static SchemaVariable svLookup(String name) {
	return (SchemaVariable)getVariables().lookup(new Name(name));
    }

    public static Sort sortLookup(String name) {
	return (Sort)getSorts().lookup(new Name(name));
    }

    public static Term parseTerm(String termstr, Services services) {
	if (termstr.equals("")) return null;
	
	StringReader br = null;
	try {	    
	    br   = new StringReader(termstr);
	    KeYParser parser = new KeYParser(ParserMode.TERM,
	                                     new KeYLexer(br,null), 
					     "No file. " +
					     "TacletForTests.parseTerm("
					     +termstr+")",
					     new Recoder2KeY(services, nss),
					     services, nss,
					     TacletForTests.getAbbrevs());
	    return parser.term();
	} catch (Exception e) {
	    System.err.println("Exception during parsing!");
	    e.printStackTrace();
	    System.exit(-1);
	    return null;
	} finally {
	    if (br != null) br.close();
	}
	
    }

    public static Term parseTerm(String termstr, NamespaceSet set) {
	if (termstr.equals("")) return null;
	StringReader br = null;
	try {	    
	    br = new StringReader(termstr);
	    KeYParser parser = new KeYParser(ParserMode.TERM,
	                                     new KeYLexer(br,null), 
					     "No file. " +
					     "TacletForTests.parseTerm("
					     +termstr+")",
					     new Recoder2KeY(services(), set),
					     services(),
					     set,
					     new AbbrevMap());
	    return parser.term();
	} catch (Exception e) {
	    System.err.println("Exception during parsing!");
	    e.printStackTrace();
	    return null;
	} finally {
	    if (br != null) br.close();
	}
	
    }

    public static Term parseTerm(String termstr) {
	return parseTerm(termstr, services());
    }

    public static ProgramElement parsePrg(String prgString) {
	Recoder2KeY r2k = new Recoder2KeY(services(), new NamespaceSet());
	return r2k.readBlockWithEmptyContext(prgString).program();
    }
}
