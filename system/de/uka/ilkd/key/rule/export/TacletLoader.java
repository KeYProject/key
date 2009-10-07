// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design 
//Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                      and Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License.
//See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.export;

import java.util.*;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortDefiningSymbols;
import de.uka.ilkd.key.proof.RuleSource;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.rule.Taclet;



public class TacletLoader {

    private boolean loadStandardRules = true;
    
    //private static InitConfig BASE_CONFIG = null;
    
    private InitConfig initConfig;
    private HashSet<String> alreadyParsed;
    
    // key: String
    // value: SetOfTaclet
    private HashMap<String, ImmutableSet<Taclet>> file2taclets;
    
    public TacletLoader() {
        initConfig = new InitConfig();
        alreadyParsed = new HashSet<String>();
        
        file2taclets = new HashMap<String, ImmutableSet<Taclet>>();
    }
    
    private void printlnIndented(int level, String msg) {
        for (int n = 0; n < level*2; n++) {
            System.out.print(' ');
        }
        System.out.println(msg);
    }
    
    
    private void setUpSorts(InitConfig initConfig) {
	Iterator<Named> it = initConfig.sortNS().allElements().iterator();
        while(it.hasNext()) {
            Sort sort = (Sort)it.next ();
            if(sort instanceof SortDefiningSymbols) {
                ((SortDefiningSymbols)sort).addDefinedSymbols (initConfig.funcNS(),
                                                               initConfig.sortNS());
            }
        }
    }

    
    
    private void loadIncludes(Includes in, int level, String filename)
        throws ProofInputException {
        if (in.getIncludes().isEmpty()) return;
        
        printlnIndented(level, filename+": loading includes");
        
        final Iterator it = in.getIncludes().iterator();
        
        while (it.hasNext()) {
            final String name = (String) it.next();
            
            loadFile(name, in.get(name), level+1);
        }        
    }
    
 
    
    private void loadLDTIncludes(Includes in, int level, String filename)
        throws ProofInputException {
        if (in.getLDTIncludes().isEmpty()) return;
        
        printlnIndented(level, filename+": loading LDTs");
        
        KeYFile[] keyFile = new KeYFile[in.getLDTIncludes().size()];
        Iterator it = in.getLDTIncludes().iterator();
        int i = 0;
        if(initConfig == null){
            initConfig = new InitConfig();
        }
        while(it.hasNext()){
            final String name = (String) it.next();
            keyFile[i] = new KeYFile(name, in.get(name), null);
            keyFile[i].setInitConfig(initConfig);
            Includes includes = keyFile[i].readIncludes();
            loadIncludes(includes, level+1, name);
            i++;
        }
        
        final ModStrategy mod = ModStrategy.NO_VARS;
        
        for (i=0; i<keyFile.length; i++) {
            keyFile[i].readSorts(mod);            
        }
        for (i=0; i<keyFile.length; i++) {              
            keyFile[i].readFuncAndPred(mod);
        }
        for (i=0; i<keyFile.length; i++) {
            
            final String name = keyFile[i].name();
            
            printlnIndented(level+1, name+": loading taclets");            
            initConfig.setTaclets(DefaultImmutableSet.<Taclet>nil());
            keyFile[i].readRulesAndProblem(mod);
            file2taclets.put(name, initConfig.getTaclets());
            
            alreadyParsed.add(name);
        }
    }


    private void loadFile(String filename, RuleSource ruleSource, int level)
        throws ProofInputException {
        if (alreadyParsed.add(filename)) {            
            KeYFile file = new KeYFile(filename, ruleSource, null);
            file.setInitConfig(initConfig);

            
            Includes includes = file.readIncludes();
            
            if (!includes.getLDTIncludes().isEmpty()) {
                loadLDTIncludes(includes, level, filename);
            }
            
            if (!includes.getIncludes().isEmpty()) {
                loadIncludes(includes, level, filename);
            }
                        
            printlnIndented(level, filename+": loading taclets");
            initConfig.setTaclets(DefaultImmutableSet.<Taclet>nil());
            
            setUpSorts(initConfig);
            file.read(ModStrategy.NO_VARS);
            file2taclets.put(filename, initConfig.getTaclets());
        } else {
            printlnIndented(level, filename+": already loaded");
        }
    }
    
    public void loadFile(String filename)
        throws ProofInputException {
        if (filename.endsWith(".key")) { 
            final String name = filename.substring(0, filename.length()-4);
            if (alreadyParsed.contains(name)) {
                return;
            }
        }
    if (!alreadyParsed.contains(filename)) {
            RuleSource ruleSource = RuleSource.initRuleFile(filename);
            loadFile(filename, ruleSource, 0);
    }
    }

    public ImmutableList<Taclet> loadRules(String filename) {
        ImmutableList<Taclet> result = null;
        
        try {
        System.out.println("Loading "+filename);
            loadFile(filename);
            
            //dumpInitConfig(initConfig);
            
            //initConfig.setTaclets(SetAsListOf.<Taclet>nil());
        
            System.out.println("Loading rules for "+filename);
            //file.readRulesAndProblem(ModStrategy.NO_VARS_FUNCS);
            
            //dumpInitConfig(initConfig);
            
            result = ImmutableSLList.<Taclet>nil();
            
            final Iterator<Taclet> it = file2taclets.get(filename).iterator();
            
            while (it.hasNext()) {
                final Taclet taclet = it.next();
                result = result.prepend(taclet);
            }
        } catch (ProofInputException e) {
            System.err.println(e);
        }
        
        return result;
    }
    
    public void setLoadStandardRules(boolean flag) {
        loadStandardRules = flag;
    }
    
    public boolean getLoadStandardRules() {
        return loadStandardRules;
    }
    
    public void addAllLoadedRules ( RuleExportModel model ) {
        
        final Iterator<Map.Entry<String, ImmutableSet<Taclet>>> it = file2taclets.entrySet().iterator();
        while ( it.hasNext() ) {
            final Map.Entry<String, ImmutableSet<Taclet>> entry = it.next();
            final String filename = entry.getKey();
            final ImmutableSet<Taclet> tacletSet = entry.getValue();
            final Iterator<Taclet> it2 = tacletSet.iterator();
            while ( it2.hasNext() ) {
                final Taclet t = it2.next ();
                model.addTaclet ( t, filename );
            }
        }
    }
    
    /** Dump namespace set from InitConfig (for debugging). */
    public static void dumpInitConfig(InitConfig initConfig) {
        dumpNamespaceSet(initConfig.namespaces(), "InitConfig");
    }
    
    /** Dump namespace set (for debugging). */
    public static void dumpNamespaceSet(NamespaceSet nss) {
        dumpNamespaceSet(nss, "NamespaceSet");
    }

    /** Dump namespace set with given name in delimiters (for debugging). */
    public static void dumpNamespaceSet(NamespaceSet nss, String name) {
        System.out.println("---- "+name+" ----");
        dumpNamespace ( nss.ruleSets() , "rule sets" );
        dumpNamespace ( nss.choices(), "choices" );
        dumpNamespace( nss.sorts(), "sorts" );
        dumpNamespace( nss.functions(), "functions" );
        System.out.println("---- End of "+name+" ----");
    }

    /** Dump namespace with given name (for debugging). */
    private static void dumpNamespace ( Namespace ns, String name ) {
	final ImmutableList<Named> elemList = ns.elements();
	Named elements[] = elemList.toArray(new Named[elemList.size()]);
        Arrays.sort(elements, new Comparator() {
            public int compare(Object a, Object b) {
                return ((Named)a).name().compareTo(((Named)b).name());
            }
        });
        
        System.out.println("-- "+name+" --");
        
        for (int n = 0; n < elements.length; n++){
            System.out.println(elements[n].name());
        }
    }

}
