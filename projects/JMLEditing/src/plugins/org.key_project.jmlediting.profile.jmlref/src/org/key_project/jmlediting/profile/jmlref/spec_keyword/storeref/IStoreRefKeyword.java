package org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref;

import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.AssignableKeyword;

/**
 * The {@link IStoreRefKeyword} is a keyword which specifies a storage location
 * and is thus used for example in an {@link AssignableKeyword}. All classes
 * which implement this interface are allowed to occur as a storage location.
 *
 * @author Moritz Lichter
 * @see StoreRefParser
 *
 */
public interface IStoreRefKeyword extends IKeyword {

}
