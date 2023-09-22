/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.model;

/**
 * Represents a sequence in an SMT model.
 *
 * @author mihai
 *
 */
public class Sequence {
    /**
     * The name of the sequence.
     */
    private String name;
    /**
     * The values contained by the sequence.
     */
    private String[] content;

    public Sequence(int length, String name) {
        super();
        this.name = name;
        if (length >= 0) {
            content = new String[length];
        }
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public int getLength() {
        return content.length;
    }

    public String get(int i) {
        return content[i];
    }

    public void set(int i, String s) {
        content[i] = s;
    }

    public String toString() {
        StringBuilder result = new StringBuilder("Seq: " + name + "\n");
        result.append("Length: ").append(content.length).append("\n");

        for (int i = 0; content != null && i < content.length; ++i) {

            result.append("[").append(i).append("] = ").append(content[i]).append("\n");
        }
        return result.toString();
    }

}
