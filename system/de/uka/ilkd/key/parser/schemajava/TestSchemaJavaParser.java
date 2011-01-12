// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.parser.schemajava;

import java.io.StringReader;

import junit.framework.TestCase;
import recoder.ServiceConfiguration;
import de.uka.ilkd.key.java.recoderext.SchemaCrossReferenceServiceConfiguration;
import de.uka.ilkd.key.java.recoderext.SchemaJavaProgramFactory;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;

public class TestSchemaJavaParser extends TestCase {

    static SchemaJavaProgramFactory factory;    
    
    public TestSchemaJavaParser(String name) {
        super(name);
    }
    
    public void setUp() {
        SchemaCrossReferenceServiceConfiguration sc = new SchemaCrossReferenceServiceConfiguration(new KeYRecoderExcHandler());
        factory = (SchemaJavaProgramFactory)sc.getProgramFactory(); 
        Namespace snvns = new Namespace();
        factory.setSVNamespace(snvns);
    }
    
    public void setUpParser(String in) {
        SchemaJavaParser.ReInit(new StringReader(in));
    }

    public void testAssert() throws ParseException {
        setUpParser("assert #nse : \"error\";");
        SchemaJavaParser.AssertStatement();
    }
    
    public void testExpression() throws ParseException {
        setUpParser("#nse");
        SchemaJavaParser.Expression();
    }

}
