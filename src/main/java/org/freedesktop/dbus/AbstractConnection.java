/*
   D-Bus Java Implementation
   Copyright (c) 2005-2006 Matthew Johnson

   This program is free software; you can redistribute it and/or modify it
   under the terms of either the GNU Lesser General Public License Version 2 or the
   Academic Free Licence Version 2.1.

   Full licence texts are included in the COPYING file with this program.
*/
package org.freedesktop.dbus;

import static org.freedesktop.dbus.Gettext.t;

import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Type;
import java.text.MessageFormat;
import java.text.ParseException;
import java.util.*;
import java.util.concurrent.*;
import java.util.regex.Pattern;

import org.freedesktop.DBus;
import org.freedesktop.dbus.exceptions.DBusException;
import org.freedesktop.dbus.exceptions.DBusExecutionException;
import org.freedesktop.dbus.exceptions.FatalDBusException;
import org.freedesktop.dbus.exceptions.FatalException;
import org.freedesktop.dbus.exceptions.NotConnected;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/** Handles a connection to DBus.
 */
public abstract class AbstractConnection {
    private final Logger logger = LoggerFactory.getLogger(getClass());

    protected class FallbackContainer {
        private final Logger                        logger    = LoggerFactory.getLogger(FallbackContainer.class);
        private final Map<String[], ExportedObject> fallbacks = new HashMap<>();

        public synchronized void add(String path, ExportedObject eo) {
            logger.debug("Adding fallback on {} of {}", path, eo);
            fallbacks.put(path.split("/"), eo);
        }

        public synchronized void remove(String path) {
            logger.debug("Removing fallback on {}", path);
            fallbacks.remove(path.split("/"));
        }

        public synchronized ExportedObject get(String path) {
            int i;
            ExportedObject bestobject = null;
            String[] pathel = path.split("/");
            for (String[] fbpath : fallbacks.keySet()) {
                logger.trace("Trying fallback path {} to match {}", Arrays.deepToString(fbpath), Arrays.deepToString(pathel));
                for (i = 0; i < pathel.length && i < fbpath.length; i++) {
                    if (!pathel[i].equals(fbpath[i])) {
                        break;
                    }
                }
                if (i > 0 && i == fbpath.length) {
                    bestobject = fallbacks.get(fbpath);
                }
                logger.trace("Matches {} bestobject now {}", i, bestobject);
            }

            logger.debug("Found fallback for {} of {}", path, bestobject);
            return bestobject;
        }
    }

    protected class ConnThread extends Thread {
        private final Logger logger = LoggerFactory.getLogger(getClass());

        public ConnThread() {
            setName("DBusConnection");
        }

        @Override
        public void run() {
            try {
                while (run) {
                    // read from the wire
                    try {
                        // this blocks on outgoing being non-empty or a message being available.
                        Message m = readIncoming();
                        if (m != null) {
                            logger.trace("Got Incoming Message: {}", m);

                            if (m instanceof DBusSignal) {
                                handleMessage((DBusSignal) m);
                            } else if (m instanceof MethodCall) {
                                handleMessage((MethodCall) m);
                            } else if (m instanceof MethodReturn) {
                                handleMessage((MethodReturn) m);
                            } else if (m instanceof Error) {
                                handleMessage((Error) m);
                            }
                        }
                    } catch (Exception e) {
                        if (EXCEPTION_DEBUG) {
                            logger.error("", e);
                        }
                        if (e instanceof FatalException) {
                            disconnect();
                        }
                    }

                }
            } catch (Exception e) {
                if (EXCEPTION_DEBUG) {
                    logger.error("", e);
                }
            }
        }
    }

    private class GlobalHandler implements org.freedesktop.DBus.Peer, org.freedesktop.DBus.Introspectable {
        private final String objectpath;

        GlobalHandler() {
            this.objectpath = null;
        }

        GlobalHandler(String _objectpath) {
            this.objectpath = _objectpath;
        }

        @Override
        public boolean isRemote() {
            return false;
        }

        @Override
        public void Ping() {
        }

        @Override
        public String Introspect() {
            String intro;
            synchronized(exportedObjects) {
                intro = objectTree.Introspect(objectpath);
            }
            if (null == intro) {
                ExportedObject eo = fallbackcontainer.get(objectpath);
                if (null != eo) {
                    intro = eo.introspectiondata;
                }
            }
            if (null == intro) {
                throw new DBus.Error.UnknownObject("Introspecting on non-existant object");
            } else {
                return "<!DOCTYPE node PUBLIC \"-//freedesktop//DTD D-BUS Object Introspection 1.0//EN\" " + "\"http://www.freedesktop.org/standards/dbus/1.0/introspect.dtd\">\n" + intro;
            }
        }

        @Override
        public String getObjectPath() {
            return objectpath;
        }
    }

    private class SenderThread extends Thread {
        private final Logger logger = LoggerFactory.getLogger(getClass());

        SenderThread() {
            setName("Sender");
        }

        @Override
        public void run() {
            logger.trace("Monitoring outbound queue");
            while (run) {
                try {
                    Message m = outgoing.take();
                    logger.debug("Got message: {}", m);
                    sendMessage(m);
                } catch (InterruptedException e) {
                }
            }
        }
    }

    /**
    * Timeout in us on checking the BUS for incoming messages and sending outgoing messages
    */
    protected static final int                                               TIMEOUT                  = 100000;
    /** Initial size of the pending calls map */
    private static final int                                                 MAX_PENDING_CALLS        = 1024;
    static final String                                                      BUSNAME_REGEX            = "^[-_a-zA-Z][-_a-zA-Z0-9]*(\\.[-_a-zA-Z][-_a-zA-Z0-9]*)*$";
    static final String                                                      CONNID_REGEX             = "^:[0-9]*\\.[0-9]*$";
    static final String                                                      OBJECT_REGEX             = "^/([-_a-zA-Z0-9]+(/[-_a-zA-Z0-9]+)*)?$";
    static final int                                                         THREADCOUNT              = Runtime.getRuntime().availableProcessors();
    static final int                                                         MAX_ARRAY_LENGTH         = 67108864;
    static final int                                                         MAX_NAME_LENGTH          = 255;

    private final ObjectTree                                                 objectTree; // synchronized using exportedObjects monitor
    private final GlobalHandler                                              globalHandlerReference;
    // CHECKSTYLE:OFF
    protected final Map<String, ExportedObject>                              exportedObjects;
    protected final Map<DBusInterface, RemoteObject>                         importedObjects;
    protected final Map<SignalTuple, Vector<DBusSigHandler<?>>>              handledSignals;
    protected final EfficientMap                                             pendingCalls;
    protected final Map<MethodCall, CallbackHandler<?>>                      pendingCallbacks;
    protected final Map<MethodCall, DBusAsyncReply<?>>                       pendingCallbackReplays; // synchronized using pendingCallbacks monitor
    protected final ThreadPoolExecutor                                       workers;
    protected final FallbackContainer                                        fallbackcontainer;
    protected volatile boolean                                               run;
    final BlockingQueue<Message>                                             outgoing;
    final Queue<Error>                                                       pendingErrors;

    protected final ConnThread                                               thread;
    protected final SenderThread                                             sender;
    protected Transport                                                      transport;
    protected final String                                                   addr;
    protected volatile boolean                                               weakreferences           = false;
    protected volatile boolean                                               connected                = false;
    // CHECKSTYLE:ON
    static final Pattern                                                     DOLLAR_PATTERN           = Pattern.compile("[$]");
    public static final boolean                                              EXCEPTION_DEBUG;
    private static final ThreadLocal<DBusCallInfo>                           callInfo                 = new ThreadLocal<>();
    static final boolean                                                     FLOAT_SUPPORT;


    static {
        FLOAT_SUPPORT = (null != System.getenv("DBUS_JAVA_FLOATS"));
        EXCEPTION_DEBUG = (null != System.getenv("DBUS_JAVA_EXCEPTION_DEBUG"));
        if (EXCEPTION_DEBUG) {
            LoggerFactory.getLogger(SenderThread.class).debug("Debugging of internal exceptions enabled");
        }
    }

    protected AbstractConnection(String address) throws DBusException {
        exportedObjects = new HashMap<>();
        importedObjects = new HashMap<>();
        globalHandlerReference = new GlobalHandler();
        exportedObjects.put(null, new ExportedObject(globalHandlerReference, weakreferences));
        handledSignals = new HashMap<>();
        pendingCalls = new EfficientMap(MAX_PENDING_CALLS);
        outgoing = new ArrayBlockingQueue<>(MAX_PENDING_CALLS);
        pendingCallbacks = new HashMap<>();
        pendingCallbackReplays = new HashMap<>();
        pendingErrors = new ConcurrentLinkedQueue<>();
        workers = new ThreadPoolExecutor(THREADCOUNT, THREADCOUNT, 0L, TimeUnit.MILLISECONDS, new LinkedBlockingQueue<Runnable>());
        objectTree = new ObjectTree();
        fallbackcontainer = new FallbackContainer();
        run = true;
        addr = address;
        thread = new ConnThread();
        sender = new SenderThread();
    }

    protected void listen() {
        // start listening
        thread.start();
        sender.start();
    }

    /**
    * Change the number of worker threads to receive method calls and handle signals.
    * Default is Runtime.getRuntime().availableProcessors()
    * @param newcount The new number of worker Threads to use.
    */
    public void changeThreadCount(byte newcount) {
        workers.setCorePoolSize(newcount);
        workers.setMaximumPoolSize(newcount);
    }

    private void addRunnable(Runnable r) {
        workers.execute(r);
    }

    String getExportedObject(DBusInterface i) throws DBusException {
        synchronized (exportedObjects) {
            for (String s : exportedObjects.keySet()) {
                if (i.equals(exportedObjects.get(s).object.get())) {
                    return s;
                }
            }
        }

        String s = importedObjects.get(i).objectpath;
        if (null != s) {
            return s;
        }

        throw new DBusException("Not an object exported or imported by this connection");
    }

    abstract DBusInterface getExportedObject(String source, String path) throws DBusException;

    /**
    * Returns a structure with information on the current method call.
    * @return the DBusCallInfo for this method call, or null if we are not in a method call.
    */
    public static DBusCallInfo getCallInfo() {
        return callInfo.get();
    }

    /**
    * If set to true the bus will not hold a strong reference to exported objects.
    * If they go out of scope they will automatically be unexported from the bus.
    * The default is to hold a strong reference, which means objects must be
    * explicitly unexported before they will be garbage collected.
    *
    * @param _weakreferences reference
    */
    public void setWeakReferences(boolean _weakreferences) {
        this.weakreferences = _weakreferences;
    }

    /**
    * Export an object so that its methods can be called on DBus.
    * @param objectpath The path to the object we are exposing. MUST be in slash-notation, like "/org/freedesktop/Local",
    * and SHOULD end with a capitalised term. Only one object may be exposed on each path at any one time, but an object
    * may be exposed on several paths at once.
    * @param object The object to export.
    * @throws DBusException If the objectpath is already exporting an object.
    *  or if objectpath is incorrectly formatted,
    */
    public void exportObject(String objectpath, DBusInterface object) throws DBusException {
        if (null == objectpath || "".equals(objectpath)) {
            throw new DBusException(t("Must Specify an Object Path"));
        }
        if (!objectpath.matches(OBJECT_REGEX) || objectpath.length() > MAX_NAME_LENGTH) {
            throw new DBusException(t("Invalid object path: ") + objectpath);
        }
        synchronized (exportedObjects) {
            if (null != exportedObjects.get(objectpath)) {
                throw new DBusException(t("Object already exported"));
            }
            ExportedObject eo = new ExportedObject(object, weakreferences);
            exportedObjects.put(objectpath, eo);
            objectTree.add(objectpath, eo, eo.introspectiondata);
        }
    }

    /**
    * Export an object as a fallback object.
    * This object will have it's methods invoked for all paths starting
    * with this object path.
    * @param objectprefix The path below which the fallback handles calls.
    * MUST be in slash-notation, like "/org/freedesktop/Local",
    * @param object The object to export.
    * @throws DBusException If the objectpath is incorrectly formatted,
    */
    public void addFallback(String objectprefix, DBusInterface object) throws DBusException {
        if (null == objectprefix || "".equals(objectprefix)) {
            throw new DBusException(t("Must Specify an Object Path"));
        }
        if (!objectprefix.matches(OBJECT_REGEX) || objectprefix.length() > MAX_NAME_LENGTH) {
            throw new DBusException(t("Invalid object path: ") + objectprefix);
        }
        ExportedObject eo = new ExportedObject(object, weakreferences);
        fallbackcontainer.add(objectprefix, eo);
    }

    /**
    * Remove a fallback
    * @param objectprefix The prefix to remove the fallback for.
    */
    public void removeFallback(String objectprefix) {
        fallbackcontainer.remove(objectprefix);
    }

    /**
    * Stop Exporting an object
    * @param objectpath The objectpath to stop exporting.
    */
    public void unExportObject(String objectpath) {
        synchronized (exportedObjects) {
            exportedObjects.remove(objectpath);
            objectTree.remove(objectpath);
        }
    }

    /**
       * Return a reference to a remote object.
       * This method will resolve the well known name (if given) to a unique bus name when you call it.
       * This means that if a well known name is released by one process and acquired by another calls to
       * objects gained from this method will continue to operate on the original process.
       *
       * @param <T> class extending {@link DBusSignal}
       * @param busname The bus name to connect to. Usually a well known bus name in dot-notation (such as "org.freedesktop.local")
       * or may be a DBus address such as ":1-16".
       * @param objectpath The path on which the process is exporting the object.$
       * @param type The interface they are exporting it on. This type must have the same full class name and exposed method signatures
       * as the interface the remote object is exporting.
       * @return A reference to a remote object.
       * @throws ClassCastException If type is not a sub-type of DBusInterface
       * @throws DBusException If busname or objectpath are incorrectly formatted or type is not in a package.
    */
    /**
    * Send a signal.
    * @param signal The signal to send.
    */
    public void sendSignal(DBusSignal signal) {
        queueOutgoing(signal);
    }

    void queueOutgoing(Message m) {
        if(connected) outgoing.add(m);
    }

    /**
    * Remove a Signal Handler.
    * Stops listening for this signal.
    *
    * @param <T> class extending {@link DBusSignal}
    * @param type The signal to watch for.
    * @param handler the handler
    * @throws DBusException If listening for the signal on the bus failed.
    * @throws ClassCastException If type is not a sub-type of DBusSignal.
    */
    public <T extends DBusSignal> void removeSigHandler(Class<T> type, DBusSigHandler<T> handler) throws DBusException {
        if (!DBusSignal.class.isAssignableFrom(type)) {
            throw new ClassCastException(t("Not A DBus Signal"));
        }
        removeSigHandler(new DBusMatchRule(type), handler);
    }

    /**
    * Remove a Signal Handler.
    * Stops listening for this signal.
    *
    * @param <T> class extending {@link DBusSignal}
    * @param type The signal to watch for.
    * @param object The object emitting the signal.
    * @param handler the handler
    * @throws DBusException If listening for the signal on the bus failed.
    * @throws ClassCastException If type is not a sub-type of DBusSignal.
    */
    public <T extends DBusSignal> void removeSigHandler(Class<T> type, DBusInterface object, DBusSigHandler<T> handler) throws DBusException {
        if (!DBusSignal.class.isAssignableFrom(type)) {
            throw new ClassCastException(t("Not A DBus Signal"));
        }
        String objectpath = importedObjects.get(object).objectpath;
        if (!objectpath.matches(OBJECT_REGEX) || objectpath.length() > MAX_NAME_LENGTH) {
            throw new DBusException(t("Invalid object path: ") + objectpath);
        }
        removeSigHandler(new DBusMatchRule(type, null, objectpath), handler);
    }

    protected abstract <T extends DBusSignal> void removeSigHandler(DBusMatchRule rule, DBusSigHandler<T> handler) throws DBusException;

    /**
    * Add a Signal Handler.
    * Adds a signal handler to call when a signal is received which matches the specified type and name.
    *
    * @param <T> class extending {@link DBusSignal}
    * @param type The signal to watch for.
    * @param handler The handler to call when a signal is received.
    * @throws DBusException If listening for the signal on the bus failed.
    * @throws ClassCastException If type is not a sub-type of DBusSignal.
    */
    public <T extends DBusSignal> void addSigHandler(Class<T> type, DBusSigHandler<T> handler) throws DBusException {
        if (!DBusSignal.class.isAssignableFrom(type)) {
            throw new ClassCastException(t("Not A DBus Signal"));
        }
        addSigHandler(new DBusMatchRule(type), handler);
    }

    /**
    * Add a Signal Handler.
    * Adds a signal handler to call when a signal is received which matches the specified type, name and object.
    *
    * @param <T> class extending {@link DBusSignal}
    * @param type The signal to watch for.
    * @param object The object from which the signal will be emitted
    * @param handler The handler to call when a signal is received.
    * @throws DBusException If listening for the signal on the bus failed.
    * @throws ClassCastException If type is not a sub-type of DBusSignal.
    */
    public <T extends DBusSignal> void addSigHandler(Class<T> type, DBusInterface object, DBusSigHandler<T> handler) throws DBusException {
        if (!DBusSignal.class.isAssignableFrom(type)) {
            throw new ClassCastException(t("Not A DBus Signal"));
        }
        String objectpath = importedObjects.get(object).objectpath;
        if (!objectpath.matches(OBJECT_REGEX) || objectpath.length() > MAX_NAME_LENGTH) {
            throw new DBusException(t("Invalid object path: ") + objectpath);
        }
        addSigHandler(new DBusMatchRule(type, null, objectpath), handler);
    }

    protected <T extends DBusSignal> void addSigHandler(DBusMatchRule rule, DBusSigHandler<T> handler) throws DBusException{
        addSigHandlerInternal(rule, handler);
    }

    protected <T extends DBusSignal> void addSigHandlerWithoutMatch(Class<? extends DBusSignal> signal, DBusSigHandler<T> handler) throws DBusException {
        addSigHandlerInternal(new DBusMatchRule(signal), handler);
    }

    private <T extends DBusSignal> void addSigHandlerInternal(DBusMatchRule rule, DBusSigHandler<T> handler){
        SignalTuple key = new SignalTuple(rule.getInterface(), rule.getMember(), rule.getObject(), rule.getSource());
        synchronized (handledSignals) {
            Vector<DBusSigHandler<? extends DBusSignal>> v = handledSignals.get(key);
            if (null == v) {
                v = new Vector<>();
                v.add(handler);
                handledSignals.put(key, v);
            } else {
                v.add(handler);
            }
        }
    }

    /**
    * Disconnect from the Bus.
    */
    public void disconnect() {
        connected = false;
        logger.debug("Sending disconnected signal");
        try {
            handleMessage(new org.freedesktop.DBus.Local.Disconnected("/"));
        } catch (Exception ex) {
            if (EXCEPTION_DEBUG) {
                logger.error("", ex);
            }
        }

        logger.debug("Disconnecting Abstract Connection");
        // run all pending tasks.
        workers.shutdown();
        try {
            workers.awaitTermination(1, TimeUnit.SECONDS);
        } catch (InterruptedException e) {
        }

        // stop the main thread
        run = false;

        // unblock the sending thread.
        sender.interrupt();

        // disconnect from the transport layer
        try {
            if (null != transport) {
                transport.disconnect();
                transport = null;
            }
        } catch (IOException exIo) {
            if (EXCEPTION_DEBUG) {
                logger.error("", exIo);
            }
        }
    }

    @Override
    public void finalize() {
        disconnect();
    }

    /**
    * Return any DBus error which has been received.
    * @return A DBusExecutionException, or null if no error is pending.
    */
    public DBusExecutionException getError() {
        Error e = pendingErrors.poll();
        return e == null? null: e.getException();
    }

    /**
    * Call a method asynchronously and set a callback.
    * This handler will be called in a separate thread.
    * @param <A> whatever
    * @param object The remote object on which to call the method.
    * @param m The name of the method on the interface to call.
    * @param callback The callback handler.
    * @param parameters The parameters to call the method with.
    */
    public <A> void callWithCallback(DBusInterface object, String m, CallbackHandler<A> callback, Object... parameters) {
        logger.trace("callWithCallback({}, {}, {})", object, m, callback);
        Class<?>[] types = new Class[parameters.length];
        for (int i = 0; i < parameters.length; i++) {
            types[i] = parameters[i].getClass();
        }
        RemoteObject ro = importedObjects.get(object);

        try {
            Method me;
            if (null == ro.iface) {
                me = object.getClass().getMethod(m, types);
            } else {
                me = ro.iface.getMethod(m, types);
            }
            RemoteInvocationHandler.executeRemoteMethod(ro, me, this, RemoteInvocationHandler.CALL_TYPE_CALLBACK, callback, parameters);
        } catch (DBusExecutionException exEe) {
            if (EXCEPTION_DEBUG) {
                logger.error("", exEe);
            }
            throw exEe;
        } catch (Exception e) {
            if (EXCEPTION_DEBUG) {
                logger.error("", e);
            }
            throw new DBusExecutionException(e.getMessage());
        }
    }

    /**
    * Call a method asynchronously and get a handle with which to get the reply.
    * @param object The remote object on which to call the method.
    * @param m The name of the method on the interface to call.
    * @param parameters The parameters to call the method with.
    * @return A handle to the call.
    */
    public DBusAsyncReply<?> callMethodAsync(DBusInterface object, String m, Object... parameters) {
        Class<?>[] types = new Class[parameters.length];
        for (int i = 0; i < parameters.length; i++) {
            types[i] = parameters[i].getClass();
        }
        RemoteObject ro = importedObjects.get(object);

        try {
            Method me;
            if (null == ro.iface) {
                me = object.getClass().getMethod(m, types);
            } else {
                me = ro.iface.getMethod(m, types);
            }
            return (DBusAsyncReply<?>) RemoteInvocationHandler.executeRemoteMethod(ro, me, this, RemoteInvocationHandler.CALL_TYPE_ASYNC, null, parameters);
        } catch (DBusExecutionException exDee) {
            if (EXCEPTION_DEBUG) {
                logger.error("", exDee);
            }
            throw exDee;
        } catch (Exception e) {
            if (EXCEPTION_DEBUG) {
                logger.error("", e);
            }
            throw new DBusExecutionException(e.getMessage());
        }
    }

    private void handleMessage(final MethodCall m) {
        logger.debug("Handling incoming method call: {}", m);

        ExportedObject eo;
        Method meth = null;
        Object o = null;

        if (null == m.getInterface() || m.getInterface().equals("org.freedesktop.DBus.Peer") || m.getInterface().equals("org.freedesktop.DBus.Introspectable")) {
            synchronized (exportedObjects) {
                eo = exportedObjects.get(null);
            }
            if (null != eo && null == eo.object.get()) {
                unExportObject(null);
                eo = null;
            }
            if (null != eo) {
                meth = eo.methods.get(new MethodTuple(m.getName(), m.getSig()));
            }
            if (null != meth) {
                o = new GlobalHandler(m.getPath());
            } else {
                eo = null;
            }
        }
        if (null == o) {
            // now check for specific exported functions

            synchronized (exportedObjects) {
                eo = exportedObjects.get(m.getPath());
            }
            if (null != eo && null == eo.object.get()) {
                logger.info("Unexporting {} implicitly", m.getPath());
                unExportObject(m.getPath());
                eo = null;
            }

            if (null == eo) {
                eo = fallbackcontainer.get(m.getPath());
            }

            if (null == eo) {
                try {
                    queueOutgoing(new Error(m, new DBus.Error.UnknownObject(m.getPath() + t(" is not an object provided by this process."))));
                } catch (DBusException exDe) {
                }
                return;
            }
            if (logger.isTraceEnabled()) {
                logger.trace("Searching for method {} with signature {}", m.getName(), m.getSig());
                logger.trace("List of methods on {}:", eo);
                for (MethodTuple mt : eo.methods.keySet()) {
                    logger.trace("   " + mt + " => " + eo.methods.get(mt));
                }
            }
            meth = eo.methods.get(new MethodTuple(m.getName(), m.getSig()));
            if (null == meth) {
                try {
                    queueOutgoing(new Error(m, new DBus.Error.UnknownMethod(MessageFormat.format(t("The method `{0}.{1}' does not exist on this object."),
                            m.getInterface(), m.getName()))));
                } catch (DBusException exDe) {
                }
                return;
            }
            o = eo.object.get();
        }

        // now execute it
        final Method me = meth;
        final Object ob = o;
        final boolean noreply = (1 == (m.getFlags() & Message.Flags.NO_REPLY_EXPECTED));
        final DBusCallInfo info = new DBusCallInfo(m);
        final AbstractConnection conn = this;

        logger.trace("Adding Runnable for method {}", meth);
        addRunnable(new Runnable() {
            @Override
            public void run() {
                logger.debug("Running method {} for remote call", me);

                try {
                    Type[] ts = me.getGenericParameterTypes();
                    m.setArgs(Marshalling.deSerializeParameters(m.getParameters(), ts, conn));
                    logger.trace("Deserialised {} to types {}", Arrays.deepToString(m.getParameters()), Arrays.deepToString(ts));
                } catch (Exception e) {
                    if (EXCEPTION_DEBUG) {
                        logger.error("", e);
                    }
                    try {
                        conn.queueOutgoing(new Error(m, new DBus.Error.UnknownMethod(t("Failure in de-serializing message: ") + e)));
                    } catch (DBusException exDe) {
                    }
                    return;
                }

                try {
                    callInfo.set(info);
                    Object result;
                    try {
                        logger.trace("Invoking Method: {} on {} with parameters {}", me, ob, Arrays.deepToString(m.getParameters()));
                        result = me.invoke(ob, m.getParameters());
                    } catch (InvocationTargetException ite) {
                        if (EXCEPTION_DEBUG) {
                            logger.error(ite.getMessage(), ite);
                        }
                        throw ite.getCause();
                    }
                    callInfo.remove();
                    if (!noreply) {
                        MethodReturn reply;
                        if (Void.TYPE.equals(me.getReturnType())) {
                            reply = new MethodReturn(m, null);
                        } else {
                            StringBuffer sb = new StringBuffer();
                            for (String s : Marshalling.getDBusType(me.getGenericReturnType())) {
                                sb.append(s);
                            }
                            Object[] nr = Marshalling.convertParameters(new Object[] {
                                    result
                            }, new Type[] {
                                    me.getGenericReturnType()
                            }, conn);

                            reply = new MethodReturn(m, sb.toString(), nr);
                        }
                        conn.queueOutgoing(reply);
                    }
                } catch (DBusExecutionException exDee) {
                    if (EXCEPTION_DEBUG) {
                        logger.error("", exDee);
                    }
                    try {
                        conn.queueOutgoing(new Error(m, exDee));
                    } catch (DBusException exDe) {
                    }
                } catch (Throwable e) {
                    if (EXCEPTION_DEBUG) {
                        logger.error("", e);
                    }
                    try {
                        conn.queueOutgoing(new Error(m, new DBusExecutionException(MessageFormat.format(t("Error Executing Method {0}.{1}: {2}"),
                                m.getInterface(), m.getName(), e.getMessage()))));
                    } catch (DBusException exDe) {
                    }
                }
            }
        });
    }

    @SuppressWarnings({
            "unchecked"
    })
    private void handleMessage(final DBusSignal s) {
        logger.debug("Handling incoming signal: {}", s);
        Vector<DBusSigHandler<? extends DBusSignal>> v = new Vector<>();
        synchronized (handledSignals) {
            Vector<DBusSigHandler<? extends DBusSignal>> t;
            t = handledSignals.get(new SignalTuple(s.getInterface(), s.getName(), null, null));
            if (null != t) {
                v.addAll(t);
            }
            t = handledSignals.get(new SignalTuple(s.getInterface(), s.getName(), s.getPath(), null));
            if (null != t) {
                v.addAll(t);
            }
            t = handledSignals.get(new SignalTuple(s.getInterface(), s.getName(), null, s.getSource()));
            if (null != t) {
                v.addAll(t);
            }
            t = handledSignals.get(new SignalTuple(s.getInterface(), s.getName(), s.getPath(), s.getSource()));
            if (null != t) {
                v.addAll(t);
            }
        }
        final AbstractConnection conn = this;
        for (final DBusSigHandler<? extends DBusSignal> h : v) {
            logger.trace("Adding Runnable for signal {} with handler {}", s, h);
            addRunnable(new Runnable() {
                @Override
                public void run() {
                    try {
                        DBusSignal rs;
                        if (s instanceof DBusSignal.internalsig || s.getClass().equals(DBusSignal.class)) {
                            rs = s.createReal(conn);
                        } else {
                            rs = s;
                        }
                        ((DBusSigHandler<DBusSignal>) h).handle(rs);
                    } catch (DBusException exDe) {
                        if (EXCEPTION_DEBUG) {
                            logger.error("", exDe);
                        }
                        try {
                            conn.queueOutgoing(new Error(s, new DBusExecutionException("Error handling signal " + s.getInterface() + "." + s.getName() + ": " + exDe.getMessage())));
                        } catch (DBusException exDe2) {
                        }
                    }
                }
            });
        }
    }

    private void handleMessage(final Error err) {
        logger.debug("Handling incoming error: " + err);
        MethodCall m;
        synchronized (pendingCalls) {
            m = pendingCalls.remove(err.getReplySerial());
        }
        if (null != m) {
            m.setReply(err);
            CallbackHandler<?> cbh;
            synchronized (pendingCallbacks) {
                cbh = pendingCallbacks.remove(m);
                logger.trace("{} = pendingCallbacks.remove({})", cbh, m);
                pendingCallbackReplays.remove(m);
            }
            // queue callback for execution
            if (null != cbh) {
                final CallbackHandler<?> fcbh = cbh;
                logger.trace("Adding Error Runnable with callback handler {}", fcbh);
                addRunnable(new Runnable() {
                    @Override
                    public void run() {
                        try {
                            logger.trace("Running Error Callback for {}", err);
                            DBusCallInfo info = new DBusCallInfo(err);
                            callInfo.set(info);

                            fcbh.handleError(err.getException());
                            callInfo.remove();

                        } catch (Exception e) {
                            if (EXCEPTION_DEBUG) {
                                logger.error("", e);
                            }
                        }
                    }
                });
            }

        } else {
            pendingErrors.offer(err);
        }
    }

    @SuppressWarnings("unchecked")
    private void handleMessage(final MethodReturn mr) {
       logger.debug("Handling incoming method return: {}", mr);
       MethodCall m;
       synchronized (pendingCalls) {
           m = pendingCalls.remove(mr.getReplySerial());
       }
       if (null != m) {
          m.setReply(mr);
          mr.setCall(m);
          @SuppressWarnings("rawtypes")
          CallbackHandler cbh;
          DBusAsyncReply<?> asr;
          synchronized (pendingCallbacks) {
             cbh = pendingCallbacks.remove(m);
             logger.trace("{} = pendingCallbacks.remove({})", cbh, m);
             asr = pendingCallbackReplays.remove(m);
          }
          // queue callback for execution
          if (null != cbh) {
             final CallbackHandler<Object> fcbh = cbh;
             final DBusAsyncReply<?> fasr = asr;
             logger.trace("Adding Runnable for method {} with callback handler {}", fasr.getMethod(), fcbh);
             addRunnable(new Runnable() {
                @Override
                public void run()
                {
                   try {
                      logger.trace("Running Callback for {}", mr);
                      DBusCallInfo info = new DBusCallInfo(mr);
                      callInfo.set(info);
                      Object convertRV = RemoteInvocationHandler.convertRV(mr.getSig(), mr.getParameters(), fasr.getMethod(), fasr.getConnection());
                      fcbh.handle(convertRV);
                      callInfo.remove();

                   } catch (Exception e) {
                      if (EXCEPTION_DEBUG) logger.error("", e);
                   }
                }
             });
          }

       } else
          try {
             queueOutgoing(new Error(mr, new DBusExecutionException(t("Spurious reply. No message with the given serial id was awaiting a reply."))));
          } catch (DBusException exDe) {}
    }

    protected void sendMessage(Message m) {
        try {
            if (!connected) {
                throw new NotConnected(t("Disconnected"));
            }
            if (m instanceof DBusSignal) {
                ((DBusSignal) m).appendbody(this);
            }

            if (m instanceof MethodCall) {
                if (0 == (m.getFlags() & Message.Flags.NO_REPLY_EXPECTED)) {
                    synchronized (pendingCalls) {
                        pendingCalls.put(m.getSerial(), (MethodCall) m);
                    }
                }
            }

            transport.mout.writeMessage(m);

        } catch (Exception e) {
            if (EXCEPTION_DEBUG) {
                logger.error("", e);
            }
            if (m instanceof MethodCall && e instanceof NotConnected) {
                try {
                    ((MethodCall) m).setReply(new Error("org.freedesktop.DBus.Local", "org.freedesktop.DBus.Local.Disconnected", 0, "s", t("Disconnected")));
                } catch (DBusException exDe) {
                }
            }
            if (m instanceof MethodCall && e instanceof DBusExecutionException) {
                try {
                    ((MethodCall) m).setReply(new Error(m, e));
                } catch (DBusException exDe) {
                }
            } else if (m instanceof MethodCall) {
                try {
                    logger.info("Setting reply to {} as an error", m);
                    ((MethodCall) m).setReply(new Error(m, new DBusExecutionException(t("Message Failed to Send: ") + e.getMessage())));
                } catch (DBusException exDe) {
                }
            } else if (m instanceof MethodReturn) {
                try {
                    transport.mout.writeMessage(new Error(m, e));
                } catch (IOException | DBusException exIo) {
                    if (EXCEPTION_DEBUG) {
                        logger.error("", exIo);
                    }
                }
            }
            if (e instanceof IOException) {
                disconnect();
            }
        }
    }

    private Message readIncoming() throws DBusException {
        if (!connected) {
            throw new NotConnected(t("No transport present"));
        }
        try {
            return transport.min.readMessage();
        } catch (IOException exIo) {
            throw new FatalDBusException(exIo.getMessage());
        }
    }

    /**
    * Returns the address this connection is connected to.
    * @return new {@link BusAddress} object
    * @throws ParseException on error
    */
    public BusAddress getAddress() throws ParseException {
        return new BusAddress(addr);
    }
}
