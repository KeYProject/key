// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.casetool.patternimplementor.patterns;

import de.uka.ilkd.key.casetool.patternimplementor.*;

/**
 * Implements a simplified database query pattern. This pattern implementation is 
 * part of the tutorial "How to create my own pattern?" outlined in the KeY Book.
 */
public class SimpleDatabaseQuery implements AbstractPatternImplementor {

    /** file name of the OCL template file */
    private static final String oclTemplateFilename = "simpleDatabaseQuery.constraint";
    
    private PIParameterGroup paramGroup;
    private ConstraintMechanism oclTemplate ;
    
    /**
     * returns the instantiated template
     */
    public SourceCode getImplementation() {

        final SourceCode src = new SourceCode();
        
        
        final String database = paramGroup.get("database").getValue();
        src.beginClass(database);
        
        src.add("(/**");

        // get table definiton instantiations
        final String tableName = paramGroup.get("tableIdentifier").getValue();
        final String[] tableStructure = ((PIParameterMultiString)
                paramGroup.get("tableStructure")).getValues();
        final String generatorExpression = paramGroup.get("generatorExpression").getValue();
        
        // add definition of table
        
        src.add(" * @definitions ");
        
        StringBuffer tblDef = new StringBuffer(tableName + ": Sequence(TupleType(");
        for (int i = 0, size = tableStructure.length; i<size; i++) {
            if (i!=0) tblDef.append(", ");
            tblDef.append(tableStructure[i]);
            
        }
        tblDef.append("))");
        tblDef.append(" = " + generatorExpression);
        src.add(" * \t " + tblDef.toString());
        
        // add database query       
        src.add(oclTemplate.getConstraints(" * ", "Database", database));
        
        src.add("*/");
        return src;
    }

    
    /**
     * creates the parameter group required for the simple database query 
     * specification pattern.     
     */
    private void createParameters() {
        paramGroup = new PIParameterGroup("simpleDatabaseQueryPattern", 
                                          "Simple Database Query Pattern");
        
        PIParameterString context = new PIParameterString("database", "Database", "Database");
        
        PIParameterGroup tableDefinitionGroup = 
            new PIParameterGroup("tableDefinition", "Table Definition");
        tableDefinitionGroup.add(new PIParameterString("tableIdentifier", 
                                                       "Tablename", 
                                                       "table"));
        tableDefinitionGroup.add(new PIParameterMultiString("tableStructure", 
                                                            "Tablestructure", 
                                                            "e1:T1, e2:T2"));        
        tableDefinitionGroup.add(new PIParameterString("generatorExpression", 
                                                       "Table generator", ""));        

        /* 
         * add parameter specifying the class used as database 
         * to the pattern's parameter group
         */
        paramGroup.add(context);

        /* add table definition group to the pattern's parameter group */
        paramGroup.add(tableDefinitionGroup);
        
        /* add query definition group to the pattern's parameter group */
        oclTemplate = new ConstraintMechanism(oclTemplateFilename, 
                                              paramGroup, this);
        
    }

    /**
     * returns the ParameterGroup to be filled out by the specifier
     * @return the ParameterGroup  
     */
    public PIParameterGroup getParameters() {
        if (paramGroup == null) {
            createParameters();
        }
        return paramGroup;
    }

    public String getName() {
        return "Specification Pattern:Simple Database Query Pattern";
    }

}
