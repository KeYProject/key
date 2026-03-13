/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;


import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.JOperatorSV;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.scripts.meta.Argument;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;

import org.checkerframework.checker.nullness.qual.MonotonicNonNull;

/**
 *
 */
public class SchemaVarCommand extends AbstractCommand {

    public SchemaVarCommand() {
        super(Parameters.class);
    }


    @Override
    public void execute(ScriptCommandAst arguments) throws ScriptException, InterruptedException {
        var args = state().getValueInjector().inject(new Parameters(), arguments);


        if (args.type == null || args.var == null) {
            throw new ScriptException("Missing argument: type var");
        }

        AbbrevMap abbrMap = state().getAbbreviations();

        if (!args.var.matches("@[a-zA-Z0-9_]")) {
            throw new ScriptException("Illegal variable name: " + args.var);
        }

        Name schemaVar = new Name("_SCHEMA_" + args.var.substring(1));

        try {
            JOperatorSV sv;
            if ("Formula".equals(args.type)) {
                sv = SchemaVariableFactory.createFormulaSV(schemaVar);
            } else {
                Sort sort = state().toSort(args.type);
                sv = SchemaVariableFactory.createTermSV(schemaVar, sort);
            }

            JTerm term = state().getProof().getServices().getTermFactory().createTerm(sv);

            abbrMap.put(term, args.var, true);
        } catch (Exception e) {
            throw new ScriptException(e);
        }

    }

    @Override
    public String getName() {
        return "schemaVar";
    }

    public static class Parameters {
        @Argument(0)
        public @MonotonicNonNull String type;
        @Argument(1)
        public @MonotonicNonNull String var;
    }

}
