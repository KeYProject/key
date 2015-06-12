package org.key_project.sed.key.evaluation.model.definition;

public class ToolPage extends AbstractPage {
   private final Tool tool;
   
   public ToolPage(Tool tool) {
      super(tool.getName(), tool.getName(), "Read the tool description carefully before continuing.", false);
      this.tool = tool;
   }
   
   public boolean isReadonly() {
      return true;
   }

   public Tool getTool() {
      return tool;
   }
}
