import Foundation

func True() async -> Bool {
    print("True")
    return true
}

func work(_ msg: String) async {
  var i = 0
  print(msg)
  while true {
    let is_true = await True()
    if (10 < i || !is_true) {
        break
    }
    print(msg)
    i += 1
  }
}

@main
struct Program {
    static func main() async {
        async let c1 = work("A")
        async let c2 = work("B")
        print("C")
        await c1
        await c2
    }
}
