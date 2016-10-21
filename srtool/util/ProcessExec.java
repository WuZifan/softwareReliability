package util;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;

public class ProcessExec {

	private static long TO_MILLI = 1000;
	private static int initialBufferLength = 2048;
	
	private ProcessBuilder processBuilder;
	
	public String stdout = null;
	public String stderr = null;
	
	public ProcessExec(String ... command)
	{
		processBuilder = new ProcessBuilder(command);
	}
	
	/**
	 * Executes the command.
	 * Pipes the String "stdin" to the process.
	 * Waits for "timeout" seconds for the process to terminate.
	 * After calling this method, the fields "stdout" and "stderr"
	 * contain the contents of the stdout and stderr of the process.
	 * The stdout is also returned.
	 * 
	 * @param stdin Piped to the process.
	 * @param timeout Time to wait in seconds.
	 * @return The stdout of the process. 
	 * @throws ProcessTimeoutException If timeout occurs. 
	 * @throws IOException
	 * @throws InterruptedException
	 */
	public String execute(String stdin, int timeout) throws ProcessTimeoutException, IOException, InterruptedException {
		
		stdout = null;
		stderr = null;
		
		Thread thread1=null;
		Thread thread2=null;
		Thread thread3=null;
		Process process = processBuilder.start();
		
		ByteArrayOutputStream stdoutStream = new ByteArrayOutputStream(initialBufferLength);
		ByteArrayOutputStream stderrStream = new ByteArrayOutputStream(initialBufferLength);
		ByteArrayInputStream stdinStream = new ByteArrayInputStream(stdin.getBytes());
		
		thread1 = FileUtil.copy(process.getInputStream(), stdoutStream);
		thread2 = FileUtil.copy(process.getErrorStream(), stderrStream);
		thread3 = FileUtil.copy(stdinStream, process.getOutputStream());
		
		// Adapted from: 
		// http://stackoverflow.com/questions/808276/how-to-add-a-timeout-value-when-using-javas-runtime-exec
		Worker worker = new Worker(process);
		worker.start();
		boolean timedout = false;
		try {
			worker.join(timeout * TO_MILLI);
			if(worker.exit == null)
			{
				timedout = true;
			}
		} catch (InterruptedException ex) {
			worker.interrupt();
			Thread.currentThread().interrupt();
			timedout = true;
			throw ex;
		} finally {
			if(timedout)
			{
				process.destroy();
			}
		}
		
		worker.join();
		
		thread1.join();
		thread2.join();
		thread3.join();
		
		if(timedout)
		{
			throw new ProcessTimeoutException("Timeout!");
		}
		stdout = stdoutStream.toString();
		stderr = stderrStream.toString();
		return stdout;
	}
	
	private static class Worker extends Thread {
		  private final Process process;
		  public volatile Integer exit;
		  private Worker(Process process) {
		    this.process = process;
		  }
		  public void run() {
		    try { 
		      exit = process.waitFor();
		    } catch (InterruptedException ignore) {
		      return;
		    }
		  }  
		}
	
}
