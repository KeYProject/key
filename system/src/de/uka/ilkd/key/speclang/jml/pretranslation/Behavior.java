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
public enum Behavior {

    NONE (""),
    BEHAVIOR ("behavior "),
    MODEL_BEHAVIOR ("model_behavior "),
    NORMAL_BEHAVIOR ("normal_behavior "),
    EXCEPTIONAL_BEHAVIOR ("exceptional_behavior "),
    BREAK_BEHAVIOR ("break_behavior "),
    CONTINUE_BEHAVIOR ("continue_behavior "),
    RETURN_BEHAVIOR ("return_behavior ");

    private final String name;


    private Behavior(String name) {
        this.name = name;
    }


    @Override
    public String toString() {
        return name;
    }
}
