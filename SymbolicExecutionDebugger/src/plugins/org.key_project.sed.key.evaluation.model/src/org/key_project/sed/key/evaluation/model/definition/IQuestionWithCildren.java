package org.key_project.sed.key.evaluation.model.definition;

public interface IQuestionWithCildren {
   public AbstractQuestion[] getChildQuestions();
   
   public int countChildQuestions();
}
