package org.key_project.sed.key.evaluation.model.input;
import org.key_project.sed.key.evaluation.model.definition.AbstractPage;
import org.key_project.util.bean.Bean;

public class AbstractPageInput<P extends AbstractPage> extends Bean {
   public static final String PROP_SHOWN_TIME = "shownTime";
   
   private final AbstractFormInput<?> formInput;
   
   private final P page;
   
   private long shownTime = 0;

   public AbstractPageInput(AbstractFormInput<?> formInput, P page) {
      assert formInput != null;
      assert page != null;
      this.formInput = formInput;
      this.page = page;
   }

   public AbstractFormInput<?> getFormInput() {
      return formInput;
   }

   public P getPage() {
      return page;
   }

   public long getShownTime() {
      return shownTime;
   }

   public void addShownTime(long timeToAdd) {
      long oldValue = getShownTime();
      this.shownTime += timeToAdd;
      firePropertyChange(PROP_SHOWN_TIME, oldValue, getShownTime());
   }

   public void setShownTime(long shownTime) {
      long oldValue = getShownTime();
      this.shownTime = shownTime;
      firePropertyChange(PROP_SHOWN_TIME, oldValue, getShownTime());
   }

   public void reset() {
      setShownTime(0);
   }
}
