//package de.uka.ilkd.key.util;
//
//
///**
// * Instances of this interface control which features are available to the user.
// *
// * Either {@link #deactivate()} or {@link #activate()} is invoked by the main
// * method of the KeY process.
// *
// * @author bruns
// */
//public interface ExperimentalFeature {
//    /**
//     * Deactivate this feature.
//     *
//     * Currently this is only called from the main method. In later versions
//     * this may be called later during execution.
//     *
//     * Subsequent calls to active must return <code>false</code>.
//     */
//    public void deactivate();
//
//    /**
//     * (Re-)Activate this feature.
//     *
//     * Currently this is only called from the main method. In later versions
//     * this may be called later during execution.
//     *
//     * Subsequent calls to active must return <code>true</code>.
//     */
//    public void activate();
//
//    /**
//     * Is this feature active?
//     *
//     * @return <code>true</code> iff this feature has been activated earlier.
//     */
//    public boolean active();
//}