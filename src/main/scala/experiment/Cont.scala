package instar

trait Monad[F[_]]:
  def pure[A](a: A): F[A]
  extension [A](fa: F[A])
    def flatMap[B](f: A => F[B]): F[B]
    def map[B](f: A => B): F[B] =
      fa.flatMap(a => pure(f(a)))

object Cont:
  opaque type Cont[R, A] = (A => R) => R
  def apply[R, A](run: (A => R) => R): Cont[R, A] = run

  def runCont[A](cont: Cont[A, A]): A = cont(identity)

  def pure[R, A](a: A): Cont[R, A] = Cont(k => k(a))

  def reset[R, A](cont: Cont[A, A]): Cont[R, A] =
    pure(runCont(cont))

  def shift[R, A](f: (A => Cont[R, R]) => Cont[R, R]): Cont[R, A] =
    //Cont(k => runCont(f(a => reset(Cont(_ => k(a))))))
    Cont(k => runCont(f(a => pure(k(a)))))

  given contMonad[R]: Monad[[A] =>> Cont[R, A]] with
    def pure[A](a: A): Cont[R, A] = Cont.pure(a)

    extension [A](fa: Cont[R, A])
      def flatMap[B](f: A => Cont[R, B]): Cont[R, B] =
        Cont(k => fa(a => f(a)(k)))

      def withFilter(p: A => Boolean): Cont[R, A] =
        Cont(k => fa(a => if p(a) then k(a) else throw new MatchError(a)))

