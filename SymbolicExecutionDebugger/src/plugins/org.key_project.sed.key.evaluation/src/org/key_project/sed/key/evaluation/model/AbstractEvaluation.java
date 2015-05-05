package org.key_project.sed.key.evaluation.model;

import java.util.List;

public abstract class AbstractEvaluation {
   private final String name;
   
   private final List<Form> forms;

   public AbstractEvaluation(String name) {
      this.name = name;
      this.forms = computeForms();
   }

   protected abstract List<Form> computeForms();

   public String getName() {
      return name;
   }
   
   public Form[] getForms() {
      return forms.toArray(new Form[forms.size()]);
   }

   public int countForms() {
      return forms.size();
   }
}
