/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.taclettranslation.assumptions;

import java.io.FileWriter;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.Calendar;
import java.util.HashSet;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.smt.SMTSettings;
import de.uka.ilkd.key.taclettranslation.IllegalTacletException;
import de.uka.ilkd.key.taclettranslation.TacletFormula;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

public final class DefaultTacletSetTranslation
        implements TacletSetTranslation, TranslationListener {

    /**
     * if <code>translate</code> is <code>true</code> the method <code>getTranslation()</code> will
     * first translate the given taclets before it returns <code>translation</code>.
     */
    private boolean translate = true;

    /**
     * Translation of the taclets stored in <code>taclets</code>.
     *
     */
    private ImmutableList<TacletFormula> translation = ImmutableSLList.nil();

    /**
     * Taclets can not be translated because checking the taclet failed.
     */
    private ImmutableList<TacletFormula> notTranslated = ImmutableSLList.nil();

    /**
     * If a instantiation failure occurs the returned information is stored in a String.
     */
    private final ImmutableList<String> instantiationFailures = ImmutableSLList.nil();


    private ImmutableSet<Sort> usedFormulaSorts = DefaultImmutableSet.nil();

    /**
     * Sorts that have been used while translating the set of taclets.
     */
    private final HashSet<Sort> usedSorts = new LinkedHashSet<>();

    /**
     * Shema variables of the type Variable that have been used while translating the set of
     * taclets.
     */
    private final HashSet<QuantifiableVariable> usedQuantifiedVariable =
        new LinkedHashSet<>();

    private final Services services;

    private final HashSet<SchemaVariable> usedFormulaSV = new LinkedHashSet<>();


    private final SMTSettings settings;

    public DefaultTacletSetTranslation(Services services, SMTSettings settings) {


        // translators = translators.append(tt);
        this.services = services;
        this.settings = settings;

    }


    @Override
    public ImmutableList<TacletFormula> getTranslation(ImmutableSet<Sort> sorts) {

        // only translate once.
        if (!translate) {
            return translation;
        }
        translate = false;
        usedSorts.clear();
        notTranslated = ImmutableSLList.nil();
        translation = ImmutableSLList.nil();

        ImmutableSet<Sort> emptySetSort = DefaultImmutableSet.nil();

        usedFormulaSorts = (sorts == null ? emptySetSort : sorts);



        for (Taclet t : settings.getTaclets()) {


            if (SupportedTaclets.REFERENCE.contains(t.name().toString(), false)) {


                try {

                    AssumptionGenerator assumptionGenerator = new AssumptionGenerator(services);
                    assumptionGenerator.addListener(this);
                    TacletFormula result =
                        assumptionGenerator.translate(t, sorts, settings.getMaxNumberOfGenerics());
                    translation = translation.append(result);

                } catch (IllegalTacletException e) {
                    notTranslated =
                        notTranslated.append(new AssumptionFormula(t, null, e.getMessage()));
                }
            } else {
                throw new RuntimeException("Taclet " + t.name() + " ist not supported");
            }
        }

        return translation;
    }



    public ImmutableList<TacletFormula> getNotTranslated() {

        return notTranslated;
    }

    public void update() {
        translate = true;
        getTranslation(usedFormulaSorts);

    }

    /**
     * Stores the translation to a file by using the key-format for problem files.
     *
     * @param dest the path of the file.
     */
    public void storeToFile(String dest) {

        FileWriter fw;
        try {
            fw = new FileWriter(dest, StandardCharsets.UTF_8);
            try {
                fw.write(toString());
            } finally {
                fw.close();
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }

    }

    public String toString() {
        ImmutableList<TacletFormula> list = getTranslation(usedFormulaSorts);
        StringBuilder toStore = new StringBuilder();
        toStore = new StringBuilder("//" + Calendar.getInstance().getTime() + "\n");

        String modelDir = services.getJavaModel().getModelDir();

        if (modelDir != null && !modelDir.isEmpty()) {
            toStore.append("\\javaSource \"").append(modelDir).append("\";\n\n");
        }

        if (usedSorts.size() > 0) {
            toStore.append("\\sorts{\n\n");
            for (Sort sort : usedFormulaSorts) {
                String name = "";
                // TODO: uncomment
                // if(sort instanceof ArraySortImpl){
                // name =
                // ((ArraySortImpl)sort).elementSort().toString();
                // }else{
                name = sort.name().toString();
                // }

                toStore.append(name).append(";\n");

            }
            toStore.append("}\n\n\n");

        }

        if (!usedFormulaSV.isEmpty()) {
            toStore.append("\\predicates{\n\n");
            for (SchemaVariable var : usedFormulaSV) {
                toStore.append(var.name().toString()).append(";\n");
            }
            toStore.append("}\n\n\n");
        }

        toStore.append("\\problem{\n\n");
        int i = 0;
        for (TacletFormula tf : list) {
            toStore.append("//").append(tf.getTaclet().name().toString()).append("\n");
            toStore.append(convertTerm(tf.getFormula(services)));
            if (i != list.size() - 1) {
                toStore.append("\n\n& //and\n\n");
            }
            i++;

        }

        toStore.append("}");

        if (notTranslated.size() > 0) {
            toStore.append("\n\n// not translated:\n");
            for (TacletFormula tf : notTranslated) {
                toStore.append("\n//").append(tf.getTaclet().name()).append(": ")
                        .append(tf.getStatus());
            }
        }

        if (instantiationFailures.size() > 0) {
            toStore.append("\n\n/* instantiation failures:\n");
            for (String s : instantiationFailures) {
                toStore.append("\n\n").append(s);
            }
            toStore.append("\n\n*/");
        }
        return toStore.toString();
    }

    private String convertTerm(Term term) {
        String ret = LogicPrinter.quickPrintTerm(term, null);
        ret = "(" + ret + ")";
        return ret;
    }

    public void eventSort(Sort sort) {
        usedSorts.add(sort);

    }

    public void eventQuantifiedVariable(QuantifiableVariable var) {
        usedQuantifiedVariable.add(var);

    }

    public void eventFormulaSV(SchemaVariable formula) {
        usedFormulaSV.add(formula);

    }

    public boolean eventInstantiationFailure(GenericSort dest, Sort sort, Taclet t, Term term) {
        /*
         * String s = ""; s += "taclet: " + t.name()+"\n"; s += "term: " + term +"\n"; s +=
         * "generic sort: " + dest + "\n"; s += "sort: "+ sort +"\n"; instantiationFailures =
         * instantiationFailures.append(s);
         */
        return false;
    }

}
