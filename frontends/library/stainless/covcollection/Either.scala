/* Copyright 2009-2026 EPFL, Lausanne */

package stainless
package covcollection

import annotation._

/** A covariant, right-biased `Either` with the API of `scala.util.Either`. */
@library
sealed abstract class Either[+A, +B] {

  def isLeft: Boolean = this match {
    case Left(_) => true
    case Right(_) => false
  }

  def isRight: Boolean = !isLeft

  def swap: Either[B, A] = this match {
    case Left(a) => Right(a)
    case Right(b) => Left(b)
  }

  def fold[C](fa: A => C, fb: B => C): C = this match {
    case Left(a) => fa(a)
    case Right(b) => fb(b)
  }

  def getOrElse[B1 >: B](or: => B1): B1 = this match {
    case Left(_) => or
    case Right(b) => b
  }

  def orElse[A1 >: A, B1 >: B](or: => Either[A1, B1]): Either[A1, B1] = this match {
    case Left(_) => or
    case Right(_) => this
  }

  def contains[B1 >: B](elem: B1): Boolean = this match {
    case Left(_) => false
    case Right(b) => b == elem
  }

  def forall(p: B => Boolean): Boolean = this match {
    case Left(_) => true
    case Right(b) => p(b)
  }

  def exists(p: B => Boolean): Boolean = this match {
    case Left(_) => false
    case Right(b) => p(b)
  }

  def map[B1](f: B => B1): Either[A, B1] = { this match {
    case Left(a) => Left(a)
    case Right(b) => Right(f(b))
  }}.ensuring { _.isRight == this.isRight }

  def flatMap[A1 >: A, B1](f: B => Either[A1, B1]): Either[A1, B1] = this match {
    case Left(a) => Left(a)
    case Right(b) => f(b)
  }

  def toOption: Option[B] = this match {
    case Left(_) => None
    case Right(b) => Some(b)
  }
}

@library
case class Left[+A, +B](value: A) extends Either[A, B]

@library
case class Right[+A, +B](value: B) extends Either[A, B]
