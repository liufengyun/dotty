## Method

      val latentValue = MethodInfo { (valInfoFn, heap) =>
        if (isChecking(ddef.symbol)) {
          // TODO: force latent effects on arguments
          debug(s"recursive call of ${ddef.symbol} found")
          Res()
        }
        else {
          val env2 = env.newEnv(heap)
          ddef.vparamss.flatten.zipWithIndex.foreach { case (param: ValDef, index: Int) =>
            val ValueInfo(state, latentValue) = valInfoFn(index)
            env2.add(param.symbol, SymInfo(assigned = true, state = state, latentValue = latentValue))
          }

          checking(ddef.symbol) { apply(ddef.rhs, env2.nonObjectRep)(ctx.withOwner(ddef.symbol)) }
        }
      }

      env.add(ddef.symbol, SymInfo(latentValue = latentValue))

## Lazy

      val latentValue = MethodInfo { (valInfoFn, heap) =>
        val env2 = heap(env.id)
        if (isChecking(vdef.symbol)) {
          debug(s"recursive forcing of lazy ${vdef.symbol} found")
          Res()
        }
        else checking(vdef.symbol) {
          apply(vdef.rhs, env2.nonObjectRep)
        }
      }
      env.add(vdef.symbol,  SymInfo(latentValue = latentValue))

## Constructor

    val latent = MethodInfo { (valInfoFn, heap) =>
      if (isChecking(cls)) {
        debug(s"recursive creation of $cls found")
        Res()
      }
      else checking(cls) {
        val obj = new ObjectRep(env.id, cls.typeRef)
        indexTemplate(cls, tmpl, obj)
        val thisInfo =  Analyzer.objectValue(obj.id, static = true)
        obj.env.add(cls, SymInfo(state = State.Partial, latentValue = thisInfo))

        val res = checkTemplate(tmpl, obj)(ctx.withOwner(cls))
        Res(latentValue = thisInfo, effects = res.effects, state = State.Filled)
      }
    }

## New

      val (tmpl: Template, envId) = env.getTree(cls)
      val clsEnv = env.heap(envId)
      indexClass(cls, tmpl, clsEnv)

      // create this object
      val obj = if (objOpt == null) new ObjectRep(clsEnv.id, tref) else objOpt

      // setup this
      val thisInfo =  Analyzer.objectValue(obj.id, static = false)
      clsEnv.add(cls, SymInfo(state = State.Partial, latentValue = thisInfo))

      // setup outer this

      // setup constructor params
      var effs = Vector.empty[Effect]
      val valInfos = args.map { arg =>
        val res = apply(arg, env)
        effs = effs ++ res.effects
        res.valueInfo
      }

      tmpl.constr.vparamss.flatten.zipWithIndex.foreach { case (param: ValDef, index: Int) =>
        val valInfo = valInfos(index)
        clsEnv.add(param.symbol, SymInfo(assigned = true, state = valInfo.state, latentValue = valInfo.latentValue))
      }

      checkTemplate(tmpl, clsEnv, obj)
