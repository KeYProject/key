package org.key_project.sed.key.evaluation.model.input;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.key_project.sed.key.evaluation.model.definition.RandomForm;
import org.key_project.sed.key.evaluation.model.definition.Tool;

public class RandomFormInput extends AbstractFormInput<RandomForm> {
   public static final String PROP_PAGE_ORDER = "pageOrder";
   public static final String PROP_PAGE_TOOL_MAP = "pageToolMap";

   private List<AbstractPageInput<?>> pageOrder;
   
   private final Map<AbstractPageInput<?>, Tool> pageToolMap = new HashMap<AbstractPageInput<?>, Tool>();
   
   public RandomFormInput(EvaluationInput evaluationInput, RandomForm form) {
      super(evaluationInput, form);
   }

   public List<AbstractPageInput<?>> getPageOrder() {
      return pageOrder;
   }

   public void setPageOrder(List<AbstractPageInput<?>> pageOrder) {
      List<AbstractPageInput<?>> newPageOrder;
      // Update page order
      if (pageOrder != null) {
         newPageOrder = new ArrayList<AbstractPageInput<?>>(pageOrder.size());
         for (AbstractPageInput<?> entry: pageOrder) {
            newPageOrder.add(getPageInput(entry.getPage()));
         }
      }
      else {
         newPageOrder = null;
      }
      // Change value
      List<AbstractPageInput<?>> oldValue = getPageOrder();
      this.pageOrder = newPageOrder;
      firePropertyChange(PROP_PAGE_ORDER, oldValue, getPageOrder());
   }
   
   public Collection<AbstractPageInput<?>> getToolPages() {
      return pageToolMap.keySet();
   }
   
   public Tool getTool(AbstractPageInput<?> page) {
      return pageToolMap.get(page);
   }
   
   public void setTool(AbstractPageInput<?> page, Tool tool) {
      Map<AbstractPageInput<?>, Tool> oldValue = new HashMap<AbstractPageInput<?>, Tool>(pageToolMap);
      pageToolMap.put(page, tool);
      firePropertyChange(PROP_PAGE_ORDER, oldValue, pageToolMap);
   }

   @Override
   public void reset() {
      setPageOrder(null);
      pageToolMap.clear();
      super.reset();
   }
}
