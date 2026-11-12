package org.scalatest

import java.util.concurrent.Executors
import org.scalatest.tools.ConcurrentDistributor

/**
 * Trait that sets number of threads in parallel execution by setting a fixed size thread pool
 *
 * Taken from https://github.com/mateuszgruszczynski/scalatesttwolevelparallelism/blob/master/src/main/scala/org/scalatest/FixedThreadPoolParallelExecution.scala
 */
trait FixedThreadPoolParallelExecution extends SuiteMixin with ParallelTestExecution{ this: Suite =>

  def threadPoolSize: Int

  // Each test runs in an instance of its own, which only needs to register that test
  override def newInstance =
    inox.TestSuite.deferringRegistration(super.newInstance)

  abstract override def run(testName: Option[String], args: Args): Status =
    super.run(testName, args.copy(
      distributor = Some(
        new ConcurrentDistributor(
          args,
          java.util.concurrent.Executors.newFixedThreadPool(threadPoolSize, Executors.defaultThreadFactory)
        )
      )
    ))

}