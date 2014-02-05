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

package de.uka.ilkd.key.taclettranslation.lemma;

import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.ProxySort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.pp.StringBackend;

public class UserDefinedSymbols {
        static class NamedComparator implements Comparator<Named>{
                static NamedComparator INSTANCE = new NamedComparator();
                @Override
                public int compare(Named o1, Named o2) {
                        return o1.name().compareTo(o2.name());
                }
                
        }
        final UserDefinedSymbols parent;
        final Set<Named> usedExtraFunctions = new TreeSet<Named>(
                        NamedComparator.INSTANCE);
        final Set<Named> usedExtraPredicates = new TreeSet<Named>(
                        NamedComparator.INSTANCE);
        final Set<Named> usedExtraSorts = new TreeSet<Named>(
                        NamedComparator.INSTANCE);
        final Set<Named> usedExtraVariables = new TreeSet<Named>(
                        NamedComparator.INSTANCE);
        final Set<Named> usedSchemaVariables = new TreeSet<Named>(
                        NamedComparator.INSTANCE);
        final ImmutableSet<Taclet> axioms;
        private final NamespaceSet referenceNamespaces;
        private String ruleHeader = null;
      

        public UserDefinedSymbols(NamespaceSet referenceNamespaces,
                        ImmutableSet<Taclet> axioms) {
                super();
                this.referenceNamespaces = referenceNamespaces;
                this.parent = null;
                this.axioms = axioms;
          
        }

        public UserDefinedSymbols(UserDefinedSymbols parent) {
                this.parent = parent;
                this.axioms = parent.axioms;
                this.referenceNamespaces = parent.referenceNamespaces;
        }

        private void addUserDefiniedSymbol(Named symbol, Set<Named> set,
                        Namespace excludeNamespace) {
                if (!contains(symbol, set)){
                        if(symbol instanceof SchemaVariable||excludeNamespace.lookup(symbol.name()) == null){
                                
                                set.add(symbol);
                
                        }
                }
                
        }

        private boolean contains(Named symbol, Set<Named> set) {
                if (parent != null && parent.contains(symbol, set)) {
                        return true;
                }

                return set.contains(symbol);
        }

        public void addFunction(Named symbol) {
                addUserDefiniedSymbol(symbol, usedExtraFunctions,
                                referenceNamespaces.functions());
        }

        public void addPredicate(Named symbol) {
                addUserDefiniedSymbol(symbol, usedExtraPredicates,
                                referenceNamespaces.functions());
        }
        
    

        public void addSort(Named symbol) {
                if (symbol != Sort.FORMULA) {
                        Sort sort = (Sort) symbol;
                        if(!(sort instanceof NullSort)){
                                for(Sort parentSort : sort.extendsSorts()){
                                        addSort(parentSort);
                                }
                       }
                        addUserDefiniedSymbol(symbol, usedExtraSorts,
                                        referenceNamespaces.sorts());
                }
        }

        public void addVariable(Named symbol) {
                addUserDefiniedSymbol(symbol, usedExtraVariables,
                                referenceNamespaces.variables());
        }

        public void addSchemaVariable(Named symbol) {
                addUserDefiniedSymbol(symbol, usedSchemaVariables,
                                referenceNamespaces.variables());
        }

        public void addSymbolsToNamespaces(NamespaceSet namespaces) {
                addSymbolsToNamespace(namespaces.functions(),
                                usedExtraFunctions);
                addSymbolsToNamespace(namespaces.functions(),
                                usedExtraPredicates);
                addSymbolsToNamespace(namespaces.sorts(), usedExtraSorts);
                addSymbolsToNamespace(namespaces.variables(),
                                usedExtraVariables);
        }

        private void addSymbolsToNamespace(Namespace namespace,
                        Collection<Named> symbols) {
                for (Named symbol : symbols) {
                        namespace.addSafely(symbol);
                }
        }

        public String getRuleHeader(Services services) {
                if (parent == null) {
                        if (ruleHeader == null) {
                                ruleHeader = createRuleHeader(services);
                        }
                        return ruleHeader;
                } else {
                        return parent.getRuleHeader(services);
                }
        }

        private String createRuleHeader(Services services) {
                StringBuffer buffer = new StringBuffer();
                buffer.append("\\rules{");
                for (Taclet taclet : axioms) {
                        buffer.append("\n\n");
                        buffer.append(createHeaderFor(taclet, services));
                }
                buffer.append("\n}");
                String result = buffer.toString();
                result = result.replaceAll("\\[", "");
                result = result.replaceAll("\\]", "");
                return result;

        }
        
        private StringBuffer createHeaderFor(Taclet taclet, Services services){
                NotationInfo info = new NotationInfo();
                StringBackend backend = new StringBackend(80);
              LogicPrinter printer = new LogicPrinter(new ProgramPrinter(),info, backend,services,true);
              printer.printTaclet(taclet);
           
              return new StringBuffer(backend.getString()+";");
        }


        public void replaceGenericByProxySorts() {
            Set<Named> result = new HashSet<Named>();
            for (Named sort : usedExtraSorts) {
                if (sort instanceof GenericSort) {
                    GenericSort genSort = (GenericSort) sort;
                    ProxySort proxySort = new ProxySort(genSort.name(), genSort.extendsSorts());
                    result.add(proxySort);
                } else {
                    result.add(sort);
                }
            }

            usedExtraSorts.clear();
            usedExtraSorts.addAll(result);
        }


        public String createHeader(Services services) {
                StringBuffer result = new StringBuffer();
            
                result.append("\n\n\\sorts{\n");
                createHeaderForSorts(result);
                result.append("}\n\n\\predicates{\n");
                createHeaderForPredicates(result);
                result.append("}\n\n\\functions{\n");
                createHeaderForFunctions(result);
                result.append("}\n\n\\schemaVariables{\n");
                createHeaderForSchemaVariables(result);
                result.append("}\n\n");
                result.append(getRuleHeader(services));
                result.append("\n\n");
                return result.toString();
        }
        
        private LinkedList<Named> ensureRightOrderOfSorts(LinkedList<Named> list){
                LinkedList<TreeSet<Named>> sortContainers = new LinkedList<TreeSet<Named>>();
                for(Named sort : list){
                      boolean added = false;
                      for(TreeSet<Named> container : sortContainers){
                              if(container.add(sort)){
                                      added = true;
                                      break;
                              }
                      }
                      if(!added){
                              sortContainers.add(new TreeSet<Named>(new Comparator<Named>() {

                                      @Override
                                      public int compare(Named o1, Named o2) {
                                              Sort s1 = (Sort) o1;
                                              Sort s2 = (Sort) o2;
                                              if(s1.extendsTrans(s2)){
                                                      return 1;
                                              }
                                              if(s2.extendsTrans(s1)){
                                                      return -1;
                                              }
                                              return 0;
                                      }
                              }));
                              sortContainers.getLast().add(sort);
                      }
                }
                LinkedList<Named> sorts = new LinkedList<Named>();
                for(TreeSet<Named> container : sortContainers){
                        sorts.addAll(container);
                }
                return sorts;
        }
        
        private void getAllSorts(LinkedList<Named> resultingSorts){
                resultingSorts.addAll(usedExtraSorts);
                if(parent != null){
                        parent.getAllSorts(resultingSorts);                        
                }
               
        }
        
        public Map<Name, Sort> getExtraSorts() {
            Map<Name, Sort> result = new HashMap<Name, Sort>();
            for (Named sort : usedExtraSorts) {
                result.put(sort.name(), (Sort) sort);
            }
            return result;
        }

        private void createHeaderForSorts(StringBuffer result){
                LinkedList<Named> sorts  = new LinkedList<Named>();              
                getAllSorts(sorts);
                sorts = ensureRightOrderOfSorts(sorts);
                
                for(Named symbol : sorts){
                        result.append(symbol.name());
                        Sort sort = (Sort) symbol;
                        if(!sort.extendsSorts().isEmpty()){
                             String res = "\\extends ";
                             boolean extendsAtLeastOneSort = false;
                             for(Sort sortParent : sort.extendsSorts()){
                                     if(sortParent !=    Sort.ANY){
                                             res += sortParent.name()+", ";
                                             extendsAtLeastOneSort = true;
                                     }                                    
                             }
                             if(extendsAtLeastOneSort){
                                     int index = res.lastIndexOf(", ");
                                     res = res.substring(0,index == -1 ? res.length() : index);
                                     result.append(res);
                             }
                        }
                        result.append(";\n");
                }                
        }
        
        private void createHeaderForFunctions(StringBuffer result){
                if(parent != null){
                    parent.createHeaderForFunctions(result);                     
                }
                for(Named symbol : usedExtraFunctions){
                        Function op = (Function) symbol;
                        result.append(op.sort().name()+" ");
                        result.append(symbol.name());
                        result.append(createSignature(op));
                        result.append(";\n");
                }                
        }
        
        private void createHeaderForPredicates(StringBuffer result){
                if(parent != null){
                    parent.createHeaderForPredicates(result);                     
                }
                for(Named symbol : usedExtraPredicates){
                        Function op = (Function) symbol;
                        result.append(symbol.name());
                        result.append(createSignature(op));
                        result.append(";\n");
                }                
        }
        
        private void createHeaderForSchemaVariables(StringBuffer result){
                if(parent != null){
                    parent.createHeaderForSchemaVariables(result);                     
                }
                for(Named symbol : usedSchemaVariables){
                        SchemaVariable sv = (SchemaVariable) symbol;
                        String prefix = sv instanceof FormulaSV ? "\\formula " : 
                                             sv instanceof TermSV? "\\term " : "\\variables ";
                        result.append(prefix);
                        result.append(sv.sort().name()+" ");
                        result.append(symbol.name());
                        result.append(";\n");
                }                
        }
        
        private String createSignature(Function op){
                String s="";
                for (int i = 0; i < op.arity(); i++) {
                         s+=(i == 0 ? "(" : ",");
                         s+=(op.argSort(i));
                         s+=(i == op.arity() - 1 ? ")"
                                                : "");
                        }
                
                return s;
        }




        public String toString() {

                String symbols = "functions:\n";
                for (Named named : usedExtraFunctions) {
                        symbols += named.name() + ", ";
                }
                symbols += "\npredicates:\n";
                for (Named named : usedExtraPredicates) {
                        symbols += named.name() + ", ";
                }
                symbols += "\nsorts:\n";
                for (Named named : usedExtraSorts) {
                        symbols += named.name() + ", ";
                }
                symbols += "\nschema variables:\n";
                for (Named named : usedSchemaVariables) {
                        symbols += named.name() + ", ";
                }
                symbols += parent != null ? "\n\n Parent: " + parent.toString()
                                : "";
                return symbols;
        }
}
