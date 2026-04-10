/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.pretranslation;


/**
 * Enum type for the JML behavior kinds.
 */
public enum Behavior {

    NONE(""), BEHAVIOR("behavior "), MODEL_BEHAVIOR("model_behavior "),
    NORMAL_BEHAVIOR("normal_behavior "), EXCEPTIONAL_BEHAVIOR("exceptional_behavior "),
    BREAK_BEHAVIOR("break_behavior "), CONTINUE_BEHAVIOR("continue_behavior "),
    RETURN_BEHAVIOR("return_behavior ");

    private final String name;


    Behavior(String name) {
        this.name = name;
    }


    @Override
    public String toString() {
        return name;
    }
}
