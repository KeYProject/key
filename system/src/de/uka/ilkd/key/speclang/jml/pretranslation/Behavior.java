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


package de.uka.ilkd.key.speclang.jml.pretranslation;


/**
 * Enum type for the JML behavior kinds.
 */
public final class Behavior {
    
    public static final Behavior NONE 
        = new Behavior("");
    public static final Behavior BEHAVIOR 
        = new Behavior("behavior ");
    public static final Behavior NORMAL_BEHAVIOR 
        = new Behavior("normal_behavior ");
    public static final Behavior EXCEPTIONAL_BEHAVIOR 
        = new Behavior("exceptional_behavior ");
    public static final Behavior BREAK_BEHAVIOR
            = new Behavior("break_behavior ");
    public static final Behavior CONTINUE_BEHAVIOR
            = new Behavior("continue_behavior ");
    public static final Behavior RETURN_BEHAVIOR
            = new Behavior("return_behavior ");
    
    
    private final String name;
  
    
    private Behavior(String name) {
        this.name = name;
    }
    
    
    @Override
    public String toString() {
        return name;
    }
}
