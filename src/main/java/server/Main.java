package server;

import org.apache.calcite.avatica.Meta;
import org.apache.calcite.avatica.remote.Driver;
import org.apache.calcite.avatica.remote.LocalService;
import org.apache.calcite.avatica.remote.Service;
import org.apache.calcite.avatica.server.HandlerFactory;
import org.apache.calcite.avatica.server.HttpServer;

import org.apache.commons.logging.Log;
import org.apache.commons.logging.LogFactory;

import com.google.common.annotations.VisibleForTesting;

import org.eclipse.jetty.server.Handler;
import server.PrivacyMetaFactoryImpl;

import java.lang.management.ManagementFactory;
import java.lang.management.RuntimeMXBean;

import java.util.Arrays;
import java.util.concurrent.CountDownLatch;

/**
 * A query server for our data lineage system over Calcite Avatica
 * Much of code borrowed from qubole/Quark code.
 */
public final class Main implements Runnable {

    protected static final Log LOG = LogFactory.getLog(Main.class);

    private final String[] argv;
    private final CountDownLatch runningLatch = new CountDownLatch(1);
    private HttpServer server = null;
    private Throwable t = null;

    /**
     * Log information about the currently running JVM.
     */
    public static void logJVMInfo() {
        // Print out vm stats before starting up.
        RuntimeMXBean runtime = ManagementFactory.getRuntimeMXBean();
        if (runtime != null) {
            LOG.info("vmName=" + runtime.getVmName() + ", vmVendor="
                    + runtime.getVmVendor() + ", vmVersion=" + runtime.getVmVersion());
            LOG.info("vmInputArguments=" + runtime.getInputArguments());
        }
    }

    public Main() {
        this(null);
    }

    public Main(String[] argv) {
        this.argv = argv;
    }

    /**
     * @return the port number this instance is bound to, or {@code -1} if the server is not running.
     */
    @VisibleForTesting
    public HttpServer getServer() {
        return server;
    }

    public void run(String[] args) throws Exception {
        logJVMInfo();
        try {

            Class<? extends Meta.Factory> factoryClass = PrivacyMetaFactoryImpl.class;

            Meta.Factory factory =
                    factoryClass.getDeclaredConstructor().newInstance();
            Meta meta = factory.create(Arrays.asList(args));

            int port = 8765;
            if (PrivacyMetaFactoryImpl.serverConfig.port != 0) {
                port = PrivacyMetaFactoryImpl.serverConfig.port;
            }
            LOG.debug("Listening on port " + port);

            final HandlerFactory handlerFactory = new HandlerFactory();
            Service service = new LocalService(meta);
            server = new HttpServer(port, getHandler(service, handlerFactory));
            Class.forName("fatjdbc.PrivacyDriver");
            server.start();
            runningLatch.countDown();
            server.join();
        } catch (Throwable t) {
            LOG.fatal("Unrecoverable service error. Shutting down.", t);
            this.t = t;
        }
    }

    /**
     * Instantiates the Handler for use by the Avatica (Jetty) server.
     *
     * @param service The Avatica Service implementation
     * @param handlerFactory Factory used for creating a Handler
     * @return The Handler to use.
     */
    Handler getHandler(Service service, HandlerFactory handlerFactory) {
        String serializationName = "PROTOBUF";
        Driver.Serialization serialization;
        try {
            serialization = Driver.Serialization.valueOf(serializationName);
        } catch (Exception e) {
            LOG.error("Unknown message serialization type for " + serializationName);
            throw e;
        }

        Handler handler = handlerFactory.getHandler(service, serialization);
        LOG.info("Instantiated " + handler.getClass() + " for Privacy Server");

        return handler;
    }

    @Override
    public void run() {
        try {
            run(argv);
        } catch (Exception e) {
            // already logged
        }
    }

    public static void main(String[] argv) throws Exception {
        new Main().run(argv);
        System.exit(0);
    }
}