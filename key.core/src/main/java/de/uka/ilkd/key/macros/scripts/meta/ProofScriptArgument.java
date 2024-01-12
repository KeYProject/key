/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts.meta;

import java.lang.reflect.Field;
import java.util.Objects;

import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;

/**
 * @author Alexander Weigl
 * @version 1 (21.04.17)
 */
public class ProofScriptArgument<T> {
    private ProofScriptCommand<T> command;
    private String name;
    private Class<?> type;
    private boolean required;
    private boolean flag;
    private Field field;
    /**
     * is an argument ellipsis
     */
    private boolean variableArguments;
    /**
     * Holds the documentation of this argument.
     */
    private String documentation;

    public ProofScriptCommand<T> getCommand() {
        return command;
    }

    public ProofScriptArgument<T> setCommand(ProofScriptCommand<T> command) {
        this.command = command;
        return this;
    }

    public String getName() {
        return name;
    }

    public ProofScriptArgument<T> setName(String name) {
        this.name = name;
        return this;
    }

    public Class<?> getType() {
        return type;
    }

    public ProofScriptArgument<T> setType(Class<?> type) {
        this.type = type;
        return this;
    }

    public boolean isRequired() {
        return required;
    }

    public ProofScriptArgument<T> setRequired(boolean required) {
        this.required = required;
        return this;
    }

    public boolean isFlag() {
        return flag;
    }

    public ProofScriptArgument<T> setFlag(boolean flag) {
        this.flag = flag;
        return this;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }

        ProofScriptArgument<?> that = (ProofScriptArgument<?>) o;

        if (required != that.required) {
            return false;
        }
        if (flag != that.flag) {
            return false;
        }
        if (!Objects.equals(command, that.command)) {
            return false;
        }
        if (!Objects.equals(name, that.name)) {
            return false;
        }
        return type == that.type;
    }

    @Override
    public int hashCode() {
        int result = command != null ? command.hashCode() : 0;
        result = 31 * result + (name != null ? name.hashCode() : 0);
        result = 31 * result + (type != null ? type.hashCode() : 0);
        result = 31 * result + (required ? 1 : 0);
        result = 31 * result + (flag ? 1 : 0);
        return result;
    }

    public Field getField() {
        return field;
    }

    public void setField(Field field) {
        this.field = field;
    }

    /**
     * Documentation for this argument.
     *
     * @return a non null string
     */
    public String getDocumentation() {
        return documentation;
    }

    /**
     * Documentation for this argument.
     *
     * @param documentation a string
     * @return this
     */
    public ProofScriptArgument<T> setDocumentation(String documentation) {
        this.documentation = documentation;
        return this;
    }

    public ProofScriptArgument<T> setVariableArguments(boolean hasVariableArguments) {
        this.variableArguments = hasVariableArguments;
        return this;
    }

    public boolean hasVariableArguments() {
        return variableArguments;
    }
}
