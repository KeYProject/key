package org.key_project.sed.key.evaluation.model.definition;

import org.key_project.sed.key.evaluation.model.tooling.IWorkbenchModifier;

public class ToolPage extends AbstractPage implements IPageWithWorkbenchModifier {
   private final Tool tool;

   private final IWorkbenchModifier workbenchModifier;
   
   private final boolean performWorkbenchModifierAutomatically;
   
   public ToolPage(Tool tool, IWorkbenchModifier workbenchModifier, boolean performWorkbenchModifierAutomatically) {
      super(tool.getName(), tool.getName(), "Read the tool description carefully before continuing.", false, false, true);
      this.tool = tool;
      this.workbenchModifier = workbenchModifier;
      this.performWorkbenchModifierAutomatically = performWorkbenchModifierAutomatically;
   }
   
   public IWorkbenchModifier getWorkbenchModifier() {
      return workbenchModifier;
   }

   public boolean isPerformWorkbenchModifierAutomatically() {
      return performWorkbenchModifierAutomatically;
   }

   public boolean isReadonly() {
      return true;
   }

   public Tool getTool() {
      return tool;
   }
}
