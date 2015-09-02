package org.key_project.sed.key.evaluation.model.definition;

import java.util.Map;

import org.key_project.util.java.CollectionUtil;

public class LabelQuestion extends AbstractQuestion {
   private final String text;
   
   private final Map<Tool, String> toolSpecificMessages;

   public LabelQuestion(String name, String text) {
      this(name, text, null);
   }

   public LabelQuestion(String name, String text, Map<Tool, String> toolSpecificMessages) {
      super(name);
      this.text = text;
      this.toolSpecificMessages = toolSpecificMessages;
   }
   
   public String getToolSpecificMessage(Tool tool) {
      if (toolSpecificMessages != null && tool != null) {
         String message = toolSpecificMessages.get(tool);
         if (message != null) {
            return message;
         }
         else {
            return getText();
         }
      }
      else {
         return getText();
      }
   }

   public String getText() {
      return text;
   }
   
   public boolean hasToolSpecificMessages() {
      return !CollectionUtil.isEmpty(toolSpecificMessages);
   }

   @Override
   public boolean isEditable() {
      return false;
   }
}
