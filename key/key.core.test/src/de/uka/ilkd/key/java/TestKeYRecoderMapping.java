// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java;

import java.util.HashMap;

import junit.framework.TestCase;

import org.junit.Assert;

import de.uka.ilkd.key.java.statement.EmptyStatement;

public class TestKeYRecoderMapping extends TestCase{

    private HashMap<Object, Object> map, revmap;
    private recoder.java.ProgramElement rp,rp2;
    private ProgramElement kp;
    private recoder.ModelElement rm, rm2;
    private ModelElement km;
    private KeYRecoderMapping mapping;



    public TestKeYRecoderMapping(String name){
        super(name);
    }


    public void setUp(){
        map = new HashMap<Object, Object>();
        revmap = new HashMap<Object, Object>();
        rp = new recoder.java.declaration.ClassDeclaration();
        kp = new EmptyStatement();
        rm = new recoder.java.statement.Case();
        km = new de.uka.ilkd.key.java.abstraction.Package("Packet");
        rp2 = new recoder.java.declaration.ClassDeclaration();
        rm2 = new recoder.java.statement.Case();
        map.put(rp,kp);
        revmap.put(kp,rp);
        map.put(rm,km);
        revmap.put(km,rm);
        mapping = new KeYRecoderMapping(map, revmap, null, false);
    }
    

    public void testtoKeY(){
        Assert.assertTrue("Fehler[1] in toKeY(recoder.java.ProgramElement)", kp.equals(mapping.toKeY(rp)));
        Assert.assertTrue("Fehler[2] in toKeY(recoder.java.ProgramElement)", null==mapping.toKeY(rp2));
        Assert.assertTrue("Fehler[3] in toKeY(recoder.ModelElement)", km.equals(mapping.toKeY(rm)));
        Assert.assertTrue("Fehler[4] in toKeY(recoder.ModelElement)", null==mapping.toKeY(rm2));
    }




    public void testtoRecoder(){
       Assert.assertTrue("Fehler[1] in toRecoder(de.uka.ilkd.key.java.ProgramElement)", rp.equals(mapping.toRecoder(kp)));
//        Assert.assertTrue("Fehler[2] in toRecoder(de.uka.ilkd.key.java.ProgramElement)", null==mapping.toRecoder(kp2));
       Assert.assertTrue("Fehler[2] in toRecoder(de.uka.ilkd.key.java.ModelElement)", rm.equals(mapping.toRecoder(km)));
//        Assert.assertTrue("Fehler[4] in toRecoder(de.uka.ilkd.key.java.ModelElement)", null==mapping.toRecoder(km2));
    }


}