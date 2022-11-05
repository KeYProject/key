// This file is part of the RECODER library and protected by the LGPL.

package recoder;

/**
 * Primary RECODER service interface.
 */
public interface Service {

    /**
     * Called by the service configuration indicating that all services are known. Services may now
     * start communicating or linking among their configuration partners. The service configuration
     * can be memorized if it has not been passed in by a constructor already.
     *
     * @param cfg the service configuration this services has been assigned to.
     */
    void initialize(ServiceConfiguration cfg);

    /**
     * Returns the service configuration this service is a part of.
     *
     * @return the configuration of this service.
     */
    ServiceConfiguration getServiceConfiguration();

}
