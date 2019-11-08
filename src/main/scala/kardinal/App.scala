package kardinal

object App {
  def main(args : Array[String]): Unit = {
    try {
      // examples.Lists.demo()
      // examples.Lists.Benchmark.main(args)
      examples.Lambda.demo()
    } catch { case e: Throwable =>
      e.printStackTrace
      sys.exit(1)
    }
  }
}