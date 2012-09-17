package org.key_project.sed.ui.provider;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.model.IValue;
import org.eclipse.debug.core.model.IVariable;
import org.eclipse.debug.internal.ui.model.elements.VariableLabelProvider;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IPresentationContext;
import org.key_project.sed.core.model.ISEDValue;
import org.key_project.sed.core.model.ISEDVariable;
import org.key_project.util.java.StringUtil;

/**
 * <p>
 * Extended {@link VariableLabelProvider} for {@link ISEDVariable} and
 * {@link ISEDValue} instances which is used to return single lined names and values.
 * </p>
 * <p>
 * Instances of this class are used if columns are shown in the variables view.
 * </p>
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class SEDVariableLabelProvider extends VariableLabelProvider {
   /**
    * {@inheritDoc}
    */
   @Override
   protected String getVariableName(IVariable variable, 
                                    IPresentationContext context) throws CoreException {
      return StringUtil.toSingleLinedString(super.getVariableName(variable, context));
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getValueText(IVariable variable, 
                                 IValue value, 
                                 IPresentationContext context) throws CoreException {
      return StringUtil.toSingleLinedString(super.getValueText(variable, value, context));
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getVariableTypeName(IVariable variable, 
                                        IPresentationContext context) throws CoreException {
      return StringUtil.toSingleLinedString(super.getVariableTypeName(variable, context));
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getValueTypeName(IVariable variable, 
                                     IValue value, 
                                     IPresentationContext context) throws CoreException {
      return StringUtil.toSingleLinedString(super.getValueTypeName(variable, value, context));
   }
}
