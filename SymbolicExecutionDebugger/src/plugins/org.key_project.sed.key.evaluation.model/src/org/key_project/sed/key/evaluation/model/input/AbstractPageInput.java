package org.key_project.sed.key.evaluation.model.input;
import org.key_project.sed.key.evaluation.model.definition.AbstractPage;
import org.key_project.util.bean.Bean;

public class AbstractPageInput<P extends AbstractPage> extends Bean {
   private final AbstractFormInput<?> formInput;
   
   private final P page;

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
}
