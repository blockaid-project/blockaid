package solver;

import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;

import java.io.*;
import java.util.Scanner;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.atomic.AtomicBoolean;

public abstract class SMTExecutor extends Thread {
//    private String smtString;
    private String solver;
    private CountDownLatch latch;
    private String[] command;
    private boolean satConclusive;
    private boolean unsatConclusive;

    private Status result = null;
    private Process process = null;
    private AtomicBoolean shuttingDown = new AtomicBoolean(false);

    protected SMTExecutor(String solver, CountDownLatch latch, String[] command, boolean satConclusive, boolean unsatConclusive) {
        this.solver = solver;
        this.latch = latch;
        this.command = command;
        this.satConclusive = satConclusive;
        this.unsatConclusive = unsatConclusive;
    }

    public void run() {
        try {
            String smtString = solver.toString() + "(check-sat)";

            startProcess();
            OutputStream stdin = process.getOutputStream();
            InputStream stdout = process.getInputStream();

            BufferedWriter bufferedStdin = new BufferedWriter(new OutputStreamWriter(stdin));
            bufferedStdin.write(smtString);
            bufferedStdin.flush();
            bufferedStdin.close();

            Scanner scanner = new Scanner(stdout);
            StringBuilder output = new StringBuilder();
            while (scanner.hasNextLine()) {
                output.append(scanner.nextLine());
            }

            process.waitFor();
            result = getResult(output.toString());
        } catch (InterruptedException e) {
            result = Status.UNKNOWN;
        } catch (Exception e) {
            Scanner scanner = new Scanner(process.getErrorStream());
            while (scanner.hasNextLine()) {
                System.err.println(scanner.nextLine());
            }
            // e.printStackTrace();
            result = Status.UNKNOWN;
        }
        if ((this.result == Status.UNSATISFIABLE && unsatConclusive) || (this.result == Status.SATISFIABLE && satConclusive)) {
            this.latch.countDown();
        } else {
            result = Status.UNKNOWN;
        }
    }

    private synchronized void startProcess() throws Exception {
        if (!this.shuttingDown.get()) {
            ProcessBuilder pb = new ProcessBuilder(command);
            process = pb.start();
        }
    }

    public synchronized void signalShutdown() {
        shuttingDown.set(true);
        this.interrupt();
        if (process != null) {
            process.destroyForcibly();
        }
    }

    public Status getResult() {
        return result;
    }

    protected Status getResult(String output) {
        switch (output.trim()) {
            case "sat":
                return Status.SATISFIABLE;
            case "unsat":
                return Status.UNSATISFIABLE;
            default:
                return Status.UNKNOWN;
        }
    }
}
